// Frontend generation verifier: plays fresh towns through the real Start flow and checks the
// rendered scene (measured from the meshes via the `?test` hook) against the backend's data.
// Usage: node scripts/verify-frontend.mjs [count=30] [base=http://localhost:5173/]
// Exit code 0 only when every check passes for every town.
import { chromium } from "playwright";
import { FAMILIES, designFor } from "../../tools/genmap.mjs";

const COUNT = Number(process.argv[2] ?? 30);
const BASE = process.argv[3] ?? "http://localhost:5173/";
const SIZES = ["easy", "medium", "hard"];
const BLOCKS = { easy: 5, medium: 7, hard: 8 };
const S = 0.1; // map units → world units (MAP_SCALE)

const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
const pageErrors = [];
page.on("pageerror", (e) => pageErrors.push(e.message));

// ---------- geometry ----------
const P = (p) => ({ x: p.x, y: p.y });
const segDist = (p, a, b) => {
  const dx = b.x - a.x, dy = b.y - a.y, L = dx * dx + dy * dy || 1;
  const t = Math.max(0, Math.min(1, ((p.x - a.x) * dx + (p.y - a.y) * dy) / L));
  return Math.hypot(p.x - a.x - t * dx, p.y - a.y - t * dy);
};
const inside = (q, poly) => {
  let r = false;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const a = poly[i], b = poly[j];
    if ((a.y > q.y) !== (b.y > q.y) && q.x < ((b.x - a.x) * (q.y - a.y)) / (b.y - a.y) + a.x) r = !r;
  }
  return r;
};
const polyDist = (q, poly) => (inside(q, poly) ? 0 : Math.min(...poly.map((a, i) => segDist(q, a, poly[(i + 1) % poly.length]))));
const area = (poly) => Math.abs(poly.reduce((s, p, i) => { const q = poly[(i + 1) % poly.length]; return s + p.x * q.y - q.x * p.y; }, 0) / 2);
const cross = (a, b, c, d) => {
  const o = (p, q, r) => Math.sign((q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x));
  return o(a, b, c) * o(a, b, d) < 0 && o(c, d, a) * o(c, d, b) < 0;
};
const shrink = (poly, k) => { const c = { x: poly.reduce((s, p) => s + p.x, 0) / poly.length, y: poly.reduce((s, p) => s + p.y, 0) / poly.length }; return poly.map((p) => ({ x: c.x + (p.x - c.x) * k, y: c.y + (p.y - c.y) * k })); };
const overlap = (A, B) => A.some((p) => inside(p, B)) || B.some((p) => inside(p, A)) || A.some((a, i) => B.some((b, j) => cross(a, A[(i + 1) % A.length], b, B[(j + 1) % B.length])));
const money = (k) => `$${Math.abs(k).toLocaleString("en-US")}k`;

// ---------- the checks ----------
function check(f, rec, hud, opts = {}) {
  const res = {};
  const fail = (k, msg) => { (res[k] ??= []).push(msg); };
  const pz = f.pr.puzzle, map = pz.map, W = f.world;
  const mapPoly = (i) => map.blocks[i].corners.map((c) => ({ x: map.points[c].x * S, y: map.points[c].y * S }));
  const segKey = (a, b) => (a < b ? `${a}-${b}` : `${b}-${a}`);
  const segIdx = new Map(map.segments.map((s, i) => [segKey(s.a, s.b), i]));

  // 1. map
  if (W.blocks.length !== map.blocks.length) fail("map", `${W.blocks.length} blocks drawn, map has ${map.blocks.length}`);
  W.blocks.forEach((b, i) => {
    const mp = mapPoly(i);
    const out = b.poly.filter((p) => polyDist(p, mp) > 0.02);
    if (out.length) fail("map", `block ${i}: ${out.length} tile corners outside its map polygon`);
    const ratio = area(b.poly) / area(mp);
    if (!(ratio > 0.2 && ratio <= 1.001)) fail("map", `block ${i}: tile/map area ${ratio.toFixed(2)}`);
  });
  for (const op of W.outerPolys) for (let i = 0; i < map.blocks.length; i++) if (overlap(op, mapPoly(i))) { fail("map", `outer block overlaps playable block ${i}`); break; }

  // 2. water
  const stream = map.segments.map((s, i) => (s.terrain === "stream" ? i : -1)).filter((i) => i >= 0);
  if (JSON.stringify([...W.river.segments].sort((a, b) => a - b)) !== JSON.stringify(stream)) fail("water", `river drawn on ${JSON.stringify(W.river.segments)}, map streams ${JSON.stringify(stream)}`);
  if (f.roadSegs.some((i) => map.segments[i].terrain === "stream")) fail("water", "a stream segment is drawn as a street");
  if (f.roadSegs.length + stream.length !== map.segments.length) fail("water", "some street segment is not drawn");
  const wet = rec.filter((r) => r.water);
  for (const k of ["cat", "car", "bus"]) { const n = wet.filter((r) => r.kind === k); if (n.length) fail("water", `${n.length} ${k} positions on water, e.g. (${n[0].x.toFixed(1)}, ${n[0].y.toFixed(1)}) ${n[0].src}`); }
  if (W.hits.river.length) fail("water", `${W.hits.river.length} building/tree points on the river, e.g. ${JSON.stringify(W.hits.river[0])}`);

  // 3. bridges
  const sites = pz.bridgeSites ?? [];
  if (W.bridges.length !== sites.length) fail("bridges", `${W.bridges.length} bridges drawn, ${sites.length} sites`);
  W.bridges.forEach((b, k) => {
    if (b.seg !== sites[k]) fail("bridges", `bridge ${k} on segment ${b.seg}, site is ${sites[k]}`);
    if (map.segments[b.seg]?.terrain !== "stream") fail("bridges", `bridge ${k} is not on the river`);
    if (b.built !== !!f.state.bridges[k] || b.ghost === b.built) fail("bridges", `bridge ${k}: built=${b.built} ghost=${b.ghost}, plan says ${!!f.state.bridges[k]}`);
    // it spans the water: the middle stands on the river, both ends on dry land
    const rl = W.river.polyline;
    const dRiver = (q) => Math.min(...rl.map(([p, r]) => segDist(q, p, r)));
    if (dRiver(b.mid) > 0.5) fail("bridges", `bridge ${k}: its middle is ${dRiver(b.mid).toFixed(2)} from the river`);
    for (const e of b.ends) if (dRiver(e) < 0.75) fail("bridges", `bridge ${k}: an end is in the water (${dRiver(e).toFixed(2)} from the river)`);
    // road to road: each end of the deck lands on a street
    const landSegs = map.segments.filter((s) => s.terrain !== "stream").map((s) => [{ x: map.points[s.a].x * S, y: map.points[s.a].y * S }, { x: map.points[s.b].x * S, y: map.points[s.b].y * S }]);
    // the quays along the banks of the bridged segment count as streets
    const sa = map.points[map.segments[b.seg].a], sb = map.points[map.segments[b.seg].b];
    const L = Math.hypot(sb.x - sa.x, sb.y - sa.y) || 1, qn = { x: -(sb.y - sa.y) / L, y: (sb.x - sa.x) / L };
    const quays = [-1, 1].map((sg) => [{ x: sa.x * S + qn.x * sg, y: sa.y * S + qn.y * sg }, { x: sb.x * S + qn.x * sg, y: sb.y * S + qn.y * sg }]);
    for (const e of b.ends) { const dmin = Math.min(...[...landSegs, ...quays].map(([p, q]) => segDist(e, p, q))); if (dmin > 0.6) fail("bridges", `bridge ${k}: an end lands ${dmin.toFixed(2)} from any street`); }
  });
  // no two decks overlap
  const deckPoly = (b) => { const d = { x: b.n.y, y: -b.n.x }, hs = 1.2, hw = 0.35; return [[-1, -1], [1, -1], [1, 1], [-1, 1]].map(([u, w]) => ({ x: b.mid.x + b.n.x * u * hs + d.x * w * hw, y: b.mid.y + b.n.y * u * hs + d.y * w * hw })); };
  for (let a = 0; a < W.bridges.length; a++) for (let c = a + 1; c < W.bridges.length; c++) if (overlap(deckPoly(W.bridges[a]), deckPoly(W.bridges[c]))) fail("bridges", `bridges ${a} and ${c} overlap`);
  if (opts.afterBuild && f.lastSent && (f.lastSent.solution.bridges ?? []).some((v, k) => v !== !!W.bridges[k]?.built)) fail("bridges", "built bridges differ from the solution sent");

  // 4. buildings
  if (opts.afterBuild) {
    const sent = f.lastSent?.solution.build ?? [];
    const FLOOR = { housing: 0.52, office: 0.62, shop: 0.52, food: 0.52, bar: 0.55 };
    W.blocks.forEach((b, i) => {
      const want = sent[i];
      if (!want) { fail("buildings", `block ${i}: nothing sent`); return; }
      if (b.kind !== want.kind || (want.kind !== "empty" && b.stories !== want.stories)) fail("buildings", `block ${i}: drawn ${b.kind}/${b.stories}, sent ${want.kind}/${want.stories}`);
      if (b.shown !== `${want.kind}:${want.stories}`) fail("buildings", `block ${i}: shown ${b.shown}`);
      const fh = FLOOR[want.kind];
      if (fh) {
        const base = 0.16 + 0.06 + want.stories * fh;
        if (b.top < base - 0.02 || b.top > base + 1.4) fail("buildings", `block ${i}: ${want.kind} ${want.stories} floors drawn ${b.top.toFixed(2)} high (expected ${base.toFixed(2)}+)`);
      }
    });
    if (JSON.stringify(sent) !== JSON.stringify(f.state.build)) fail("buildings", "solution sent differs from the plan on screen");
  }

  // 5. overlaps
  for (const k of ["metro", "bridge", "road"]) if (W.hits[k].length) {
    const tags = [...new Set(W.hits[k].map((h) => h.tag))].join(",");
    fail("overlaps", `${W.hits[k].length} points of ${tags} on the ${k}, e.g. ${JSON.stringify(W.hits[k][0])}`);
  }
  W.blocks.forEach((b, i) => {
    const H = b.hulls.map((h) => shrink(h, 0.96));
    for (let a = 0; a < H.length; a++) for (let c = a + 1; c < H.length; c++) if (overlap(H[a], H[c])) fail("overlaps", `block ${i}: buildings ${a} and ${c} overlap`);
  });
  for (let a = 0; a < W.outerPolys.length; a++) for (let c = a + 1; c < W.outerPolys.length; c++) if (overlap(shrink(W.outerPolys[a], 0.97), shrink(W.outerPolys[c], 0.97))) { fail("overlaps", `outer blocks ${a} and ${c} overlap`); }

  // 6. transit
  f.routes.forEach((r, i) => {
    for (let k = 1; k < r.nodes.length; k++) if (!segIdx.has(segKey(r.nodes[k - 1], r.nodes[k]))) fail("transit", `route ${i}: ${r.nodes[k - 1]}-${r.nodes[k]} is not a street`);
    const nodePts = r.nodes.map((n) => ({ x: map.points[n].x * S, y: map.points[n].y * S }));
    // near the river the ribbon keeps to the banks and goes over the bridges: skip points close to water
    const riverPts = map.segments.filter((s) => s.terrain === "stream").flatMap((s) => [map.points[s.a], map.points[s.b]]).map((q) => ({ x: q.x * S, y: q.y * S }));
    const off = r.path.filter((p) => riverPts.every((q) => Math.hypot(p.x - q.x, p.y - q.y) > 3.2)).map((p) => Math.min(...nodePts.slice(1).map((q, k) => segDist(p, nodePts[k], q)))).filter((d) => d > 0.32);
    if (off.length) fail("transit", `route ${i}: ribbon leaves its streets by ${off[0].toFixed(2)}`);
    // a route over the river only along stream segments (bridge sites)
    for (let k = 1; k < r.nodes.length; k++) { const si = segIdx.get(segKey(r.nodes[k - 1], r.nodes[k])); if (si !== undefined && map.segments[si].terrain === "stream" && !sites.includes(si)) fail("transit", `route ${i} crosses water off a bridge site`); }
  });
  const want6 = [...(pz.metroSites ?? pz.stationSites)].sort((a, b) => a - b);
  if (JSON.stringify([...f.stationSpots].sort((a, b) => a - b)) !== JSON.stringify(want6)) fail("transit", `station sites drawn ${JSON.stringify(f.stationSpots)}, metroSites ${JSON.stringify(want6)}`);
  const me = pz.metroEntry;
  if (W.metro && me && (me.x || me.y)) {
    const d = { x: me.x * S - f.center.x, y: me.y * S - f.center.y }, L = Math.hypot(d.x, d.y);
    const dot = (d.x * W.metro.dir.x + d.y * W.metro.dir.y) / L;
    if (dot < 0.98) fail("transit", `metro comes from a different side than metroEntry (cos ${dot.toFixed(3)})`);
  }
  if (W.metro && f.state.station !== null) {
    const br = W.metro.branch;
    if (br.length < 2) fail("transit", "station built but no metro line to it");
    else for (let k = 1; k < br.length - 1; k++) if (!map.points.some((p) => Math.hypot(p.x * S - br[k].x, p.y * S - br[k].y) < 0.02)) { fail("transit", "metro line under town leaves the streets"); break; }
  }

  // 7. cats and cars
  const rep = f.built?.report ?? f.lastSent?.reply?.report;
  if (rep?.cats) {
    const ids = new Map(rep.cats.map((c) => [String(c.id), c]));
    const seen = new Set([...f.day.drawn.map((c) => c.id), ...f.day.dropped]);
    if (seen.size !== ids.size || [...seen].some((id) => !ids.has(id))) fail("cats", `animated ${f.day.drawn.length}+${f.day.dropped.length} cats, report has ${ids.size}`);
    for (const c of f.day.drawn) {
      const r = ids.get(c.id);
      if (!r) continue;
      if (r.home !== c.home) fail("cats", `cat ${c.id}: home ${c.home}, report ${r.home}`);
      c.legs.forEach((l) => {
        if (typeof l.from === "number" && l.start && polyDist(l.start, mapPoly(l.from)) > 0.9) fail("cats", `cat ${c.id}: leg starts away from block ${l.from}`);
        if (typeof l.to === "number" && l.end && polyDist(l.end, mapPoly(l.to)) > 0.9) fail("cats", `cat ${c.id}: leg ends away from block ${l.to}`);
      });
    }
    for (const id of f.day.dropped) {
      const r = ids.get(id);
      if (r?.legs.some((l) => typeof l.from === "number" && typeof l.to === "number" && l.from !== l.to)) fail("cats", `cat ${id} has a trip between blocks but isn't animated`);
    }
  }
  if (rep?.streets) {
    const cars = new Map(rep.streets.map((s) => [s.segment, s.cars]));
    const per = new Map();
    for (const t of f.day.traffic) {
      const si = t.seg;
      if (si < 0 || !(cars.get(si) > 0)) fail("cats", `a looping car on segment ${si}, which has no cars in report.streets`);
      if (si >= 0 && map.segments[si].terrain === "stream" && !f.state.bridges[sites.indexOf(si)]) fail("cats", `a car on unbridged water (segment ${si})`);
      per.set(si, (per.get(si) ?? 0) + 1);
    }
    for (const [si, n] of per) if (n > 3) fail("cats", `${n} cars on segment ${si}`);
  }

  // 8. HUD
  if (opts.afterBuild && f.built && hud) {
    const r = f.built;
    if (r.rating && hud.ring !== String(r.rating.rating)) fail("hud", `rating shows ${hud.ring}, reply ${r.rating.rating}`);
    const want = [r.report.happiness.toLocaleString("en-US"), r.report.productivity.toLocaleString("en-US")];
    if (JSON.stringify(hud.pair) !== JSON.stringify(want)) fail("hud", `happiness/productivity show ${hud.pair}, reply ${want}`);
    const left = pz.budget - r.report.cost;
    const m = `${left < 0 ? "−" : ""}${money(left)}`;
    if (hud.money[0] !== m) fail("hud", `money shows ${hud.money[0]}, expected ${m}`);
  }
  if (hud) { const bad = hud.text.match(/\b(lean|proofs?|proven|proved|theorem)\b/i); if (bad) fail("hud", `visible text says "${bad[0]}"`); }
  return res;
}

const fingerprint = (f) => JSON.stringify({
  blocks: f.world.blocks.map((b) => [b.shown, b.verts, b.top]), river: f.world.river.segments, outer: f.world.outskirtsVerts,
  bridges: f.world.bridges.map((b) => [b.seg, b.along, b.across]), metro: f.world.metro,
});

async function facts() { return page.evaluate(() => JSON.parse(JSON.stringify(window.__sb.facts()))); }

/** Check one open town: as generated, then after a random layout is built. */
async function verifyOpenTown(label, seedForLayout) {
  await page.mouse.move(1435, 600);
  await page.waitForTimeout(1500);
  const f0 = await facts();
  const rec0 = await page.evaluate(() => window.__sb.record(2500));
  const r0 = check(f0, rec0, await page.evaluate(() => window.__sb.hud()));
  await page.evaluate((s) => window.__sb.placeRandom(s), seedForLayout);
  await page.waitForTimeout(1200);
  await page.click("#build");
  await page.waitForFunction(() => window.__sb.isBuilt(), null, { timeout: 120000 });
  await page.waitForTimeout(2600);
  await page.waitForFunction(() => window.__sb.settled(), null, { timeout: 30000 });
  const f1 = await facts();
  const rec1 = await page.evaluate(() => window.__sb.record(4000));
  const r1 = check(f1, rec1, await page.evaluate(() => window.__sb.hud()), { afterBuild: true });
  const merged = {};
  for (const r of [r0, r1]) for (const [k, v] of Object.entries(r)) (merged[k] ??= []).push(...v);
  return { label, f: f0, res: merged };
}

const CHECKS = ["map", "water", "bridges", "buildings", "overlaps", "transit", "cats", "hud", "determinism", "randomness"];
const rows = [];
const prints = new Map();

// fresh towns through the real Start flow
/** A page reload mid-check (the dev server reloads when source files change) restarts that town. */
async function retry(fn) {
  for (let t = 0; ; t++) {
    try { return await fn(); } catch (e) {
      if (t >= 2 || !/context was destroyed|navigation|Target closed/i.test(String(e))) throw e;
      console.log(`\n(page reloaded, retrying: ${String(e).split("\n")[0]})`);
    }
  }
}
for (let k = 0; k < COUNT; k++) await retry(async () => {
  const size = SIZES[k % 3];
  await page.goto(`${BASE}?test&nocoach`);
  await page.waitForSelector(".title-card.on", { timeout: 60000 });
  await page.click(".title-card.on [data-act='start']");
  await page.click(`[data-pick='${size}']`);
  await page.waitForSelector(".intro-card", { timeout: 400000 });
  const seed = Number((await page.textContent(".intro-card h2")).replace(/\D/g, ""));
  await page.click("[data-act='go']");
  const t = await verifyOpenTown(`#${seed}`, seed ^ 0x5eed);
  const fam = designFor(seed);
  const fp = JSON.stringify(t.f.pr.puzzle.map.points);
  if (prints.has(fp)) (t.res.randomness ??= []).push(`same town as ${prints.get(fp)}`);
  prints.set(fp, t.label);
  if (t.f.pr.puzzle.map.blocks.length !== BLOCKS[size]) (t.res.map ??= []).push(`${t.f.pr.puzzle.map.blocks.length} blocks for ${size}`);
  rows.push({ town: t.label, size, shape: `${fam.family}/${fam.river}`, res: t.res });
  process.stdout.write(`\r${k + 1}/${COUNT} towns checked`);
});
console.log();

// replays: one per shape not seen yet, plus two more; each loaded twice (determinism)
const seenShapes = new Set(rows.map((r) => r.shape.split("/")[0]));
const replaySeeds = [];
for (const fam of FAMILIES) if (!seenShapes.has(fam)) { for (let s = 1000; s < 200000; s += 7) if (designFor(s).family === fam) { replaySeeds.push(s); break; } }
replaySeeds.push(4242, 777001);
for (const [k, seed] of replaySeeds.entries()) await retry(async () => {
  const size = SIZES[k % 3];
  const url = `${BASE}?seed=${seed}&size=${size}&test&nocoach&nointro`;
  const prints2 = [];
  let res = {};
  for (let pass = 0; pass < 2; pass++) {
    await page.goto(url);
    await page.waitForSelector("#tools .tile", { timeout: 400000 });
    await page.waitForTimeout(2000);
    prints2.push(fingerprint(await facts()));
    if (pass === 0) res = (await verifyOpenTown(`?seed=${seed}`, seed)).res;
  }
  if (prints2[0] !== prints2[1]) (res.determinism ??= []).push("the same seed drew a different scene");
  const fam = designFor(seed);
  rows.push({ town: `?seed=${seed} (x2)`, size, shape: `${fam.family}/${fam.river}`, res });
});
await browser.close();

// ---------- summary ----------
const cell = (r, k) => (r.res[k]?.length ? "FAIL" : "ok");
console.log(["town".padEnd(22), "size".padEnd(7), "shape".padEnd(20), ...CHECKS.map((c) => c.slice(0, 6).padEnd(7))].join(""));
for (const r of rows) console.log([r.town.padEnd(22), r.size.padEnd(7), r.shape.padEnd(20), ...CHECKS.map((c) => cell(r, c).padEnd(7))].join(""));
let failures = 0;
for (const r of rows) for (const [k, v] of Object.entries(r.res)) if (v.length) { failures += v.length; console.log(`  ${r.town} ${k}: ${[...new Set(v)].slice(0, 3).join(" | ")}`); }
const shapes = new Set(rows.map((r) => r.shape.split("/")[0]));
console.log(`\n${rows.length} towns, shapes covered: ${[...shapes].join(", ")} (${shapes.size}/${FAMILIES.length})`);
if (pageErrors.length) { console.log(`page errors: ${[...new Set(pageErrors)].slice(0, 5).join(" | ")}`); failures += pageErrors.length; }
console.log(failures ? `${failures} failures` : "ALL CHECKS PASS");
process.exit(failures ? 1 : 0);
