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
const waiting = []; // reply callbacks, oldest first; the binary answers in order

function start() {
  child = spawn(BIN, [], { stdio: ["pipe", "pipe", "inherit"] });
  child.on("error", (e) => console.error(`[bridge] spawn failed: ${e.message}`));
  createInterface({ input: child.stdout }).on("line", (line) => waiting.shift()?.(line));
  child.on("exit", (code, sig) => {
    console.error(`[bridge] binary exited (${code ?? sig}); restarting`);
    // Requests in flight are lost: answer them with an error.
    for (const cb of waiting.splice(0)) cb(JSON.stringify({ ok: false, error: "engine restarted" }));
    setTimeout(start, 500);
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
        const m = generateMap(seed, 5 + (seed % 5));
        line = JSON.stringify({ cmd: "generate", seed, routes: m.routes,
          map: { points: m.points, segments: m.segments, blocks: m.blocks } });
      }
    } catch { /* not JSON: let Lean report the error */ }
    waiting.push((reply) => { if (ws.readyState === ws.OPEN) ws.send(reply); });
    child.stdin.write(line + "\n");
  });
});
console.log(`[bridge] ws://localhost:${PORT}  ->  ${BIN}`);
