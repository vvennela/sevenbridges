// Make the starter pack: towns made ahead of time, so the first Start in the
// browser is instant. Each town is made by the native Lean program with the same
// requests the game uses: `generate` (3 maps at most, as the bridge does) and
// `solve`, then `export` for the puzzle with every field. Each town is then
// checked with `load` (the command the browser uses to open it) in a new Lean
// process: Lean must accept the stored best plan and give back the same puzzle.
//
//   node wasm/make-pack.mjs [easy] [medium] [hard]     (default 20 20 20)
//   -> web/public/pack/{easy,medium,hard}.json
//
// A pack entry: { seed, puzzle, best, bestScore, randomMedian }. `puzzle` is the
// Lean puzzle as `export` returned it; `best` is the layout `solve` returned.
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import { webcrypto } from "node:crypto";
import { cpus } from "node:os";
import { mkdirSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { generateMap } from "../tools/genmap.mjs";

const here = (p) => fileURLToPath(new URL(p, import.meta.url));
const BIN = process.env.SB_BIN ?? here("../.lake/build/bin/sevenbridges");
const OUT = here("../web/public/pack/");
const SIZES = { easy: 5, medium: 7, hard: 8 };
const want = { easy: Number(process.argv[2] ?? 20), medium: Number(process.argv[3] ?? 20), hard: Number(process.argv[4] ?? 20) };
const PAR = Math.max(1, Math.min(8, Math.floor(cpus().length / 2)));

function lean() {
  const c = spawn(BIN, [], { stdio: ["pipe", "pipe", "inherit"] });
  const waiting = [];
  createInterface({ input: c.stdout }).on("line", (l) => waiting.shift()(l));
  return {
    ask: (req) => new Promise((res) => { waiting.push((l) => res(JSON.parse(l))); c.stdin.write(JSON.stringify(req) + "\n"); }),
    stop: () => c.stdin.end(),
  };
}
const freshSeed = () => webcrypto.getRandomValues(new Uint32Array(1))[0] || 1;

async function makeOne(size) {
  const L = lean();
  try {
    const seed0 = freshSeed();
    let g = null;
    for (let tries = 0; tries < 3; tries++) {
      const seed = (seed0 + 7919 * tries) >>> 0;
      const m = generateMap(seed, SIZES[size]);
      g = await L.ask({ cmd: "generate", seed, routes: m.routes, map: { points: m.points, segments: m.segments, blocks: m.blocks } });
      if (!(g.ok && g.data.generated === false)) break;
    }
    if (!g?.ok || !g.data.generated) return null;
    const s = await L.ask({ cmd: "solve" });
    const best = s.data.best.solution;
    const bestScore = g.data.verified.bestScore;
    if (s.data.best.score !== bestScore) throw new Error("solve and generate disagree");
    const puzzle = (await L.ask({ cmd: "export" })).data.puzzle;
    // the check the browser will do: Lean accepts it and returns the same puzzle
    const L2 = lean();
    const l = await L2.ask({ cmd: "load", puzzle, best, bestScore });
    const back = l.ok ? (await L2.ask({ cmd: "export" })).data.puzzle : null;
    L2.stop();
    if (!l.ok || JSON.stringify(l.data.puzzle) !== JSON.stringify(g.data.puzzle) || JSON.stringify(back) !== JSON.stringify(puzzle)) throw new Error(`load check failed: ${JSON.stringify(l).slice(0, 200)}`);
    return { seed: g.data.seed, puzzle, best, bestScore, randomMedian: g.data.info.randomPlay?.median };
  } finally { L.stop(); }
}

mkdirSync(OUT, { recursive: true });
for (const size of Object.keys(SIZES)) {
  const towns = [];
  const seen = new Set();
  const t0 = Date.now();
  while (towns.length < want[size]) {
    const batch = await Promise.all(Array.from({ length: Math.min(PAR, want[size] - towns.length) }, () => makeOne(size)));
    for (const t of batch) if (t && !seen.has(t.seed)) { seen.add(t.seed); towns.push(t); }
    process.stdout.write(`\r${size}: ${towns.length}/${want[size]}`);
  }
  const file = `${OUT}${size}.json`;
  writeFileSync(file, JSON.stringify({ version: 1, size, towns }));
  console.log(`  ${((Date.now() - t0) / 1000).toFixed(0)} s -> ${file}`);
}
