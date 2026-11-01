// Differential test: the native Lean program and the WebAssembly build must give
// the same reply, byte for byte, to the same request lines. Also times both.
//
//   node wasm/compare.mjs [seeds per size, default 3]
//
// For each size and seed it makes a town (with the same 3-map retry as the
// game), then asks: solve, evaluate the best layout (with and without rating),
// evaluate a changed layout, and evaluate a broken request. Then the demo town.
// The requests are made once (from the native replies) and sent to both.
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import { fileURLToPath } from "node:url";
import { generateMap } from "../tools/genmap.mjs";

const here = (p) => fileURLToPath(new URL(p, import.meta.url));
const BIN = process.env.SB_BIN ?? here("../.lake/build/bin/sevenbridges");
const WASM = process.env.SB_WASM ?? here("../web/public/engine/sevenbridges.mjs");
const PER_SIZE = Number(process.argv[2] ?? 3);
const SIZES = { easy: 5, medium: 7, hard: 8 };

// ---- the native program ----
const child = spawn(BIN, [], { stdio: ["pipe", "pipe", "inherit"] });
const waiting = [];
createInterface({ input: child.stdout }).on("line", (l) => waiting.shift()(l));
const native = (line) => new Promise((res) => { waiting.push(res); child.stdin.write(line + "\n"); });

// ---- the wasm build ----
const { default: createModule } = await import(WASM);
let t0 = performance.now();
const M = await createModule();
M._sb_init();
const wasmStart = performance.now() - t0;
const wasm = (line) => M.ccall("sb_request", "string", ["string"], [line]);

// ---- run ----
const rows = [];     // { cmd, label, nativeMs, wasmMs, same }
let failures = 0;
async function both(label, req) {
  const line = typeof req === "string" ? req : JSON.stringify(req);
  let t = performance.now();
  const a = await native(line);
  const nativeMs = performance.now() - t;
  t = performance.now();
  const b = wasm(line);
  const wasmMs = performance.now() - t;
  const same = a === b;
  if (!same) {
    failures++;
    console.log(`DIFFERENT ${label}\n native: ${a.slice(0, 300)}\n wasm:   ${b.slice(0, 300)}`);
  }
  rows.push({ cmd: label.split(" ")[0], label, nativeMs, wasmMs, same, bytes: a.length });
  return JSON.parse(a);
}

function generateLine(seed, blocks) {
  const m = generateMap(seed, blocks);
  return { cmd: "generate", seed, routes: m.routes, map: { points: m.points, segments: m.segments, blocks: m.blocks } };
}

for (const [size, blocks] of Object.entries(SIZES)) {
  for (let k = 0; k < PER_SIZE; k++) {
    const seed0 = (1000 + 7 * k + blocks * 100003) >>> 0;
    let g;
    for (let tries = 0; tries < 3; tries++) {
      const seed = (seed0 + 7919 * tries) >>> 0;
      g = await both(`generate ${size} seed=${seed}`, generateLine(seed, blocks));
      if (!(g.ok && g.data.generated === false)) break;
    }
    if (!g.ok || !g.data.generated) { console.log(`no town for ${size} ${seed0}`); continue; }
    const s = await both(`solve ${size}`, { cmd: "solve" });
    const best = s.data.best.solution;
    await both(`evaluate ${size} best`, { cmd: "evaluate", solution: best });
    await both(`evaluate ${size} best+rate`, { cmd: "evaluate", solution: best, rate: true });
    const changed = { ...best, build: [...best.build].reverse(), routesOn: best.routesOn.map((x) => !x) };
    await both(`evaluate ${size} changed+rate`, { cmd: "evaluate", solution: changed, rate: true });
    await both(`evaluate ${size} broken`, { cmd: "evaluate", solution: { build: 3 } });
    await both(`puzzle ${size}`, { cmd: "puzzle" });
  }
}
await both("demo", { cmd: "demo" });
const ds = await both("solve demo", { cmd: "solve" });
await both("evaluate demo best+rate", { cmd: "evaluate", solution: ds.data.best.solution, rate: true });
await both("unknown", { cmd: "nope" });
await both("not-json", "{oops");
child.stdin.end();

// ---- report ----
const fmt = (x) => x >= 1000 ? `${(x / 1000).toFixed(2)} s` : `${x.toFixed(1)} ms`;
console.log(`\nwasm start (load + init): ${fmt(wasmStart)}\n`);
console.log("| request | native | wasm (node) | wasm/native | same reply |");
console.log("|---|---:|---:|---:|---|");
for (const r of rows) console.log(`| ${r.label} | ${fmt(r.nativeMs)} | ${fmt(r.wasmMs)} | ${(r.wasmMs / r.nativeMs).toFixed(1)}x | ${r.same ? "yes" : "NO"} |`);
console.log(`\n${rows.length} requests, ${rows.length - failures} identical replies, ${failures} different.`);
process.exit(failures ? 1 : 0);
