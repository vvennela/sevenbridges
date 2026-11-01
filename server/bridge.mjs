// WebSocket <-> Lean binary bridge. No game logic: each WebSocket message is
// written as one line to the binary's stdin, and each stdout line is sent back
// to whoever asked, in order. Usage: node bridge.mjs [port]  (env: SB_BIN, PORT)
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import { fileURLToPath } from "node:url";
import { WebSocketServer } from "ws";
import { generateMap } from "../tools/genmap.mjs";

const BIN = process.env.SB_BIN ??
  fileURLToPath(new URL("../.lake/build/bin/sevenbridges", import.meta.url));
const PORT = Number(process.argv[2] ?? process.env.PORT ?? 8787);

let child = null;
let alive = false;
let restartTimer = null;
const waiting = []; // reply callbacks, oldest first; the binary answers in order

/** Answer every request in flight with an error (the engine went away). */
function failPending(why) {
  for (const cb of waiting.splice(0)) cb(JSON.stringify({ ok: false, error: why }));
}

/** Start the engine again soon. Keeps retrying (e.g. while the binary is being rebuilt). */
function scheduleRestart(delay) {
  if (restartTimer) return;
  restartTimer = setTimeout(() => { restartTimer = null; start(); }, delay);
}

function start() {
  const c = spawn(BIN, [], { stdio: ["pipe", "pipe", "inherit"] });
  child = c;
  alive = true;
  c.on("error", (e) => {
    console.error(`[bridge] engine unavailable (${e.message}); retrying`);
    alive = false;
    failPending("engine restarting, try again");
    scheduleRestart(1000);
  });
  c.stdin.on("error", () => { /* broken pipe: handled by exit/error */ });
  createInterface({ input: c.stdout }).on("line", (line) => waiting.shift()?.(line));
  c.on("exit", (code, sig) => {
    if (child !== c) return;
    console.error(`[bridge] binary exited (${code ?? sig}); restarting`);
    alive = false;
    failPending("engine restarted, try again");
    scheduleRestart(500);
  });
}
start();

const wss = new WebSocketServer({ port: PORT });
wss.on("connection", (ws) => {
  ws.on("message", (msg) => {
    let line = msg.toString().replace(/\r?\n/g, " ");
    // "newPuzzle": make a map (untrusted geometry; Lean checks it), then ask
    // Lean to generate a puzzle on it.
    try {
      const req = JSON.parse(line);
      if (req.cmd === "newPuzzle") {
        const seed = Number(req.seed) >>> 0;
        // Puzzle sizes: easy 5 blocks, medium 7, hard 9 (DESIGN.md §8.5).
        const sizes = { easy: 5, medium: 7, hard: 9 };
        const blocks = sizes[req.size] ?? [5, 7, 9][seed % 3];
        const m = generateMap(seed, blocks);
        line = JSON.stringify({ cmd: "generate", seed, routes: m.routes,
          map: { points: m.points, segments: m.segments, blocks: m.blocks } });
      }
    } catch { /* not JSON: let Lean report the error */ }
    const reply = (r) => { if (ws.readyState === ws.OPEN) ws.send(r); };
    if (!alive || !child?.stdin?.writable) {
      reply(JSON.stringify({ ok: false, error: "engine restarting, try again" }));
      scheduleRestart(200);
      return;
    }
    waiting.push(reply);
    child.stdin.write(line + "\n");
  });
});
console.log(`[bridge] ws://localhost:${PORT}  ->  ${BIN}`);
