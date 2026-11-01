// WebSocket <-> Lean binary bridge. No game logic: each request is written as
// one line to a Lean binary's stdin, and each stdout line is sent back in order.
//
// Speed: proving a new town takes seconds, so the bridge prepares one town of
// each size ahead of time, each in its own copy of the binary. "New town" hands
// the player a ready town (and its binary) at once, and starts preparing the
// next one. Every town is still generated and proven by the same Lean binary.
//
// Usage: node bridge.mjs [port]   (env: SB_BIN, PORT)
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import { webcrypto } from "node:crypto";
import { fileURLToPath } from "node:url";
import { WebSocketServer } from "ws";
import { generateMap } from "../tools/genmap.mjs";

const BIN = process.env.SB_BIN ??
  fileURLToPath(new URL("../.lake/build/bin/sevenbridges", import.meta.url));
const PORT = Number(process.argv[2] ?? process.env.PORT ?? 8787);
const SIZES = { easy: 5, medium: 7, hard: 8 };

/** One running copy of the Lean binary. Answers requests in order. */
class Engine {
  constructor(name, restart = false) {
    this.name = name;
    this.restart = restart;   // the shared engine comes back if it dies
    this.waiting = [];
    this.dead = false;
    this.start();
  }
  start() {
    const c = spawn(BIN, [], { stdio: ["pipe", "pipe", "inherit"] });
    this.child = c;
    this.alive = true;
    const fail = (why) => { for (const cb of this.waiting.splice(0)) cb(JSON.stringify({ ok: false, error: why })); };
    c.on("error", (e) => {
      this.alive = false;
      fail("engine restarting, try again");
      if (this.restart && !this.dead) setTimeout(() => this.start(), 1000);
      else console.error(`[bridge] ${this.name}: ${e.message}`);
    });
    c.stdin.on("error", () => {});
    createInterface({ input: c.stdout }).on("line", (line) => this.waiting.shift()?.(line));
    c.on("exit", () => {
      if (this.child !== c) return;
      this.alive = false;
      fail("engine restarted, try again");
      if (this.restart && !this.dead) setTimeout(() => this.start(), 500);
    });
  }
  /** Send one request line; resolves with the reply line. */
  ask(line) {
    return new Promise((resolve) => {
      if (!this.alive || !this.child?.stdin?.writable) {
        resolve(JSON.stringify({ ok: false, error: "engine restarting, try again" }));
        return;
      }
      this.waiting.push(resolve);
      this.child.stdin.write(line + "\n");
    });
  }
  stop() { this.dead = true; this.child?.kill(); }
}

const freshSeed = () => webcrypto.getRandomValues(new Uint32Array(1))[0] || 1;

/** The Lean request that makes a town on the map for this seed. */
function generateLine(seed, blocks) {
  const m = generateMap(seed, blocks);
  return JSON.stringify({ cmd: "generate", seed, routes: m.routes,
    map: { points: m.points, segments: m.segments, blocks: m.blocks } });
}

/** Make a town on `engine`. If Lean finds no level it can prove in time on a
 * map, try another map (at most 3). The reply's "seed" says which map was used. */
async function makeTown(engine, seed, blocks) {
  let reply = "";
  for (let tries = 0; tries < 3; tries++) {
    reply = await engine.ask(generateLine((seed + 7919 * tries) >>> 0, blocks));
    try {
      const j = JSON.parse(reply);
      if (!(j.ok && j.data && j.data.generated === false)) return reply;
    } catch { return reply; }
  }
  return reply;
}

// ---- the pool of towns made ahead of time ----

const DEPTH = 2;        // towns kept ready per size
const ready = {};       // size -> [{ engine, reply }]
const making = {};      // size -> number of towns being prepared
let queue = Promise.resolve();
const waiters = {};     // size -> resolvers waiting for the next ready town

/** Keep DEPTH towns of this size ready, each in its own engine. One town is
 * prepared at a time across all sizes, so the CPU is shared fairly. */
function prepare(size) {
  ready[size] ??= [];
  making[size] ??= 0;
  while (ready[size].length + making[size] < DEPTH) {
    making[size]++;
    queue = queue.then(async () => {
      const engine = new Engine(`pool-${size}`);
      const t0 = Date.now();
      const reply = await makeTown(engine, freshSeed(), SIZES[size]);
      let ok = false;
      try { const j = JSON.parse(reply); ok = j.ok && j.data?.generated; } catch {}
      making[size]--;
      if (ok) {
        console.log(`[bridge] ${size} town ready in ${Date.now() - t0} ms`);
        const w = waiters[size]?.shift();
        if (w) w({ engine, reply }); else ready[size].push({ engine, reply });
      } else engine.stop();
      prepare(size);
    });
  }
}

/** A ready town of this size: at once if one is waiting, else the next one made. */
function takeReady(size) {
  const t = ready[size]?.shift();
  prepare(size);
  if (t) return Promise.resolve(t);
  return new Promise((resolve) => { (waiters[size] ??= []).push(resolve); });
}
for (const size of Object.keys(SIZES)) prepare(size);

// ---- connections ----

const lobby = new Engine("lobby", true);   // title screen, demo, anything before a town

const wss = new WebSocketServer({ port: PORT });
wss.on("connection", (ws) => {
  let own = null;   // this player's engine, once they have a town
  const send = (r) => { if (ws.readyState === ws.OPEN) ws.send(r); };
  // Replies must go back in request order, so requests from one connection run one at a time.
  let chain = Promise.resolve();

  const handle = async (line) => {
    let req = null;
    try { req = JSON.parse(line); } catch { /* let Lean report the error */ }
    if (req?.cmd === "newPuzzle") {
      const size = Object.keys(SIZES).includes(req.size) ? req.size : ["easy", "medium", "hard"][(req.seed >>> 0) % 3];
      if (!req.replay) {
        // A town made ahead of time (or the next one being made): hand it over.
        const take = await takeReady(size);
        own?.stop();
        own = take.engine;
        return take.reply;
      }
      // A specific seed (replay): make exactly that town in this player's own engine.
      own?.stop();
      own = new Engine("player");
      return makeTown(own, Number(req.seed) >>> 0, SIZES[size]);
    }
    return (own ?? lobby).ask(line.replace(/\r?\n/g, " "));
  };

  ws.on("message", (msg) => {
    const line = msg.toString();
    chain = chain.then(() => handle(line)).then(send, (e) => send(JSON.stringify({ ok: false, error: String(e) })));
  });
  ws.on("close", () => { chain.then(() => own?.stop()); });
});
console.log(`[bridge] ws://localhost:${PORT}  ->  ${BIN}`);
