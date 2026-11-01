// Checks that new games are really different from each other.
// Asks the running bridge for many new towns with fresh random seeds, then checks:
//   - no two towns are the same (map, river, groups, prices, simulation seed),
//   - sizes, building kinds and groups come out spread out, not stuck on a few.
// Usage: node randomcheck.mjs [count] [ws://localhost:8787]
import { webcrypto } from "node:crypto";
import WebSocket from "../server/node_modules/ws/index.js";

const count = Number(process.argv[2] ?? 40);
const url = process.argv[3] ?? "ws://localhost:8787";
const sizes = ["easy", "medium", "hard"];

const ws = new WebSocket(url);
await new Promise((ok, fail) => { ws.on("open", ok); ws.on("error", fail); });
const waiting = [];
ws.on("message", (m) => waiting.shift()?.(JSON.parse(String(m))));
const ask = (req) => new Promise((ok) => { waiting.push(ok); ws.send(JSON.stringify(req)); });

const seed32 = () => webcrypto.getRandomValues(new Uint32Array(1))[0] || 1;
const fingerprint = (pz) => JSON.stringify({
  points: pz.map.points, blocks: pz.map.blocks.map((b) => b.corners),
  river: pz.map.segments.filter((s) => s.terrain === "stream").map((s) => [s.a, s.b]),
  groups: pz.groups.map((g) => [g.name, g.share, g.types?.map((t) => [t.name, t.share, t.cares, t.hates])]),
  allowed: pz.allowed, budget: pz.budget, simSeed: pz.simSeed, metro: pz.metroSites, bridges: pz.bridgeSites,
});

const seen = new Map();
const tally = { size: {}, groups: {}, kinds: {}, blocks: {} };
const bump = (t, k) => { t[k] = (t[k] ?? 0) + 1; };
let made = 0, failed = 0, duplicates = 0;
const t0 = Date.now();

for (let i = 0; i < count; i++) {
  const size = sizes[i % 3];
  const seed = seed32();
  const r = await ask({ cmd: "newPuzzle", seed, size });
  if (!r.ok || !r.data.generated) { failed++; continue; }
  const pz = r.data.puzzle.puzzle;
  const fp = fingerprint(pz);
  if (seen.has(fp)) { duplicates++; console.log(`DUPLICATE: seed ${seed} matches seed ${seen.get(fp)}`); }
  seen.set(fp, r.data.seed ?? seed);
  made++;
  bump(tally.size, size);
  bump(tally.blocks, pz.map.blocks.length);
  for (const g of pz.groups) bump(tally.groups, g.name);
  for (const k of new Set(pz.allowed.map((b) => b.kind))) bump(tally.kinds, k);
  process.stdout.write(`\r${made} made, ${failed} not made, ${duplicates} duplicates`);
}
ws.close();
console.log(`\n\nin ${((Date.now() - t0) / 1000).toFixed(0)} s`);
console.log("distinct towns:", seen.size, "of", made, duplicates === 0 ? "(all different)" : "(REPEATS FOUND)");
const simSeeds = [...seen.keys()].map((k) => JSON.parse(k).simSeed);
console.log("distinct simulation seeds:", new Set(simSeeds).size, "of", simSeeds.length);
for (const [name, t] of Object.entries(tally)) console.log(`${name}:`, JSON.stringify(t));
process.exit(duplicates === 0 ? 0 : 1);
