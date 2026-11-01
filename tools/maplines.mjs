// Prints one JSON {map, routes} per line, for `lake exe bbtime`.
// Usage: node maplines.mjs n1:seed1 n2:seed2 ...
import { generateMap } from "./genmap.mjs";
for (const arg of process.argv.slice(2)) {
  const [n, seed] = arg.split(":").map(Number);
  const m = generateMap(seed, n);
  console.log(JSON.stringify({ map: { points: m.points, segments: m.segments, blocks: m.blocks }, routes: m.routes }));
}
