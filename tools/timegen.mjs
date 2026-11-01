// Times the Lean generator on random maps.
// Usage: node timegen.mjs <binary> [blocks:seed ...]
import { spawnSync } from "node:child_process";
import { generateMap } from "./genmap.mjs";
const bin = process.argv[2];
const cases = process.argv.length > 3 ? process.argv.slice(3).map((x) => x.split(":").map(Number)).map(([n, s]) => [s, n])
  : [[1, 6], [2, 7], [3, 7], [4, 8], [5, 9], [6, 7], [8, 9], [9, 5], [10, 5], [11, 7], [12, 9], [13, 7], [14, 9]];
for (const [seed, n] of cases) {
  const m = generateMap(seed, n);
  const req = JSON.stringify({ cmd: "generate", map: { points: m.points, segments: m.segments, blocks: m.blocks }, routes: m.routes, seed });
  const t0 = Date.now();
  const out = spawnSync(bin, { input: req + "\n", encoding: "utf8", maxBuffer: 1 << 26 });
  const ms = Date.now() - t0;
  const reply = JSON.parse(out.stdout);
  if (!reply.ok) { console.log(seed, n, "ERROR", reply.error); continue; }
  const d = reply.data;
  const p = d.puzzle;
  console.log(`seed ${seed} blocks ${n}: ${ms} ms, generated=${d.generated}, attempts=${d.info.attempts}, work=${d.info.work}` +
    (p ? `, candidates=${p.candidateCount}, budget=${p.puzzle.budget}` : ""));
}
