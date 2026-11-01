// Map generator (DESIGN.md §2.2). Not trusted: Lean checks every map it gets.
// A river runs along a chain of interior road segments, from one edge of town
// to the other (segments with terrain "stream").
// Usage: node genmap.mjs <seed> <blockCount>   → prints a map as JSON.
import { Delaunay } from "d3-delaunay";

function rng(seed) {
  // mulberry32: small seeded random number generator
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// Clip polygon `subject` by convex polygon `clip` (Sutherland–Hodgman).
function clipPolygon(subject, clip) {
  const inside = (p, a, b) => (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0]) >= 0;
  const cross = (p, q, a, b) => {
    const a1 = b[1] - a[1], b1 = a[0] - b[0], c1 = a1 * a[0] + b1 * a[1];
    const a2 = q[1] - p[1], b2 = p[0] - q[0], c2 = a2 * p[0] + b2 * p[1];
    const d = a1 * b2 - a2 * b1;
    return [(c1 * b2 - c2 * b1) / d, (a1 * c2 - a2 * c1) / d];
  };
  let out = subject;
  for (let i = 0; i < clip.length; i++) {
    const a = clip[i], b = clip[(i + 1) % clip.length];
    const input = out; out = [];
    for (let j = 0; j < input.length; j++) {
      const p = input[j], q = input[(j + 1) % input.length];
      const pin = inside(p, a, b), qin = inside(q, a, b);
      if (pin) { out.push(p); if (!qin) out.push(cross(p, q, a, b)); }
      else if (qin) out.push(cross(p, q, a, b));
    }
    if (out.length === 0) break;
  }
  return out;
}

const area = (poly) => poly.reduce((s, p, i) => {
  const q = poly[(i + 1) % poly.length]; return s + p[0] * q[1] - q[0] * p[1];
}, 0) / 2;

/** Town shapes. Each seed picks one, so towns differ in structure, not just in detail. */
export const FAMILIES = ["round", "oval", "crescent", "lshape", "peninsula", "twin", "grid"];
/** River patterns. "none": no river (and so no bridge sites). */
export const RIVERS = ["none", "across", "straight", "bend", "fork"];

const R = 100;
const TARGET_AREA = Math.PI * R * R; // every shape is scaled to about the same area

/** Smooth radial outline: rad(t) for t in [0, 2π). */
function radial(f, K = 36) {
  const out = [];
  for (let k = 0; k < K; k++) { const t = (k / K) * Math.PI * 2; const r0 = f(t); out.push([r0 * Math.cos(t), r0 * Math.sin(t)]); }
  return out;
}
const angDiff = (a, b) => { let d = Math.abs(a - b) % (2 * Math.PI); return d > Math.PI ? 2 * Math.PI - d : d; };
const rotate = (poly, a) => poly.map(([x, y]) => [x * Math.cos(a) - y * Math.sin(a), x * Math.sin(a) + y * Math.cos(a)]);
/** A polygon with each edge split into short pieces (so Voronoi cells meet it in many places). */
function densify(poly, step = 18) {
  const out = [];
  poly.forEach((p, i) => {
    const q = poly[(i + 1) % poly.length], L = Math.hypot(q[0] - p[0], q[1] - p[1]), k = Math.max(1, Math.round(L / step));
    for (let j = 0; j < k; j++) out.push([p[0] + (q[0] - p[0]) * j / k, p[1] + (q[1] - p[1]) * j / k]);
  });
  return out;
}

/** The outline of a town of this family (CCW, about TARGET_AREA, centered near 0,0). */
function outlineFor(family, r) {
  const ph = [r() * 6.28, r() * 6.28, r() * 6.28];
  const wob = (t, k = 1) => 1 + k * (0.06 * Math.sin(2 * t + ph[0]) + 0.04 * Math.sin(3 * t + ph[1]) + 0.025 * Math.sin(5 * t + ph[2]));
  const turn = r() * Math.PI * 2;
  let o;
  switch (family) {
    case "oval": { // a long town along a riverside: an ellipse about twice as long as wide
      const a = 1.5, b = 0.62;
      o = rotate(radial((t) => wob(t, 0.6) / Math.hypot(Math.cos(t) / a, Math.sin(t) / b)), turn);
      break;
    }
    case "crescent": { // wrapped around a bay or lake on one side
      const d = turn;
      o = radial((t) => { const x = angDiff(t, d); return wob(t, 0.4) * (x < 1.1 ? 1 - 0.68 * Math.cos((x / 1.1) * Math.PI / 2) ** 2 : 1); }, 48);
      break;
    }
    case "peninsula": { // a promontory: a teardrop pointing out into the water
      const d = turn;
      o = radial((t) => wob(t, 0.3) * (0.6 + 0.85 * Math.cos(angDiff(t, d) / 2) ** 8), 48);
      break;
    }
    case "lshape": { // two wings meeting at a corner
      const w = 1, L = 2.1, j = () => (r() - 0.5) * 0.12;
      const P = [[0, 0], [L + j(), 0], [L + j(), w], [w + j(), w], [w + j(), L + j()], [0, L]];
      o = rotate(densify(P.map(([x, y]) => [x - 0.8, y - 0.8]), 0.18), turn);
      break;
    }
    case "twin": { // two halves facing each other across the river: a stadium
      const a = 1.35, b = 0.85;
      o = rotate(radial((t) => wob(t, 0.3) / Math.pow(Math.pow(Math.abs(Math.cos(t) / a), 3) + Math.pow(Math.abs(Math.sin(t) / b), 3), 1 / 3)), turn);
      break;
    }
    case "grid": { // a planned town: a rounded rectangle
      const a = 1.25, b = 0.95;
      o = rotate(radial((t) => wob(t, 0.25) / Math.pow(Math.pow(Math.abs(Math.cos(t) / a), 5) + Math.pow(Math.abs(Math.sin(t) / b), 5), 1 / 5), 48), turn);
      break;
    }
    default:
      o = radial((t) => wob(t), 24);
  }
  if (area(o) < 0) o.reverse();
  // center and scale to the target area
  const cx = o.reduce((s, p) => s + p[0], 0) / o.length, cy = o.reduce((s, p) => s + p[1], 0) / o.length;
  const k = Math.sqrt(TARGET_AREA / area(o));
  return o.map(([x, y]) => [(x - cx) * k, (y - cy) * k]);
}

function pointIn(p, poly) {
  let inside = false;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const [xi, yi] = poly[i], [xj, yj] = poly[j];
    if ((yi > p[1]) !== (yj > p[1]) && p[0] < ((xj - xi) * (p[1] - yi)) / (yj - yi) + xi) inside = !inside;
  }
  return inside;
}

/** Does a polygon cross itself (or fold back on an edge)? */
function selfCrossing(poly) {
  const n = poly.length;
  const hit = (a, b, c, d) => {
    const o = (p, q, r2) => Math.sign((q[0] - p[0]) * (r2[1] - p[1]) - (q[1] - p[1]) * (r2[0] - p[0]));
    return o(a, b, c) * o(a, b, d) < 0 && o(c, d, a) * o(c, d, b) < 0;
  };
  for (let i = 0; i < n; i++) for (let j = i + 2; j < n; j++) {
    if (i === 0 && j === n - 1) continue;
    if (hit(poly[i], poly[(i + 1) % n], poly[j], poly[(j + 1) % n])) return true;
  }
  return false;
}

/** Make the blocks for one try: seed points (dense core or even), a few relaxation steps,
 * optionally in a stretched space (long thin blocks), clipped to the outline. */
function makeCells(outline, n, r, style) {
  // stretch: Voronoi in a space squashed along one axis gives blocks long along it
  const stretch = style.thin ? 1.7 : 1, sa = r() * Math.PI;
  const fw = ([x, y]) => { const u = x * Math.cos(sa) + y * Math.sin(sa), v = -x * Math.sin(sa) + y * Math.cos(sa); return [u / stretch, v]; };
  const bw = ([u, v]) => { u *= stretch; return [u * Math.cos(sa) - v * Math.sin(sa), u * Math.sin(sa) + v * Math.cos(sa)]; };
  const O = outline.map(fw);
  if (area(O) < 0) O.reverse();
  const xs = O.map((p) => p[0]), ys = O.map((p) => p[1]);
  const box = [Math.min(...xs), Math.min(...ys), Math.max(...xs), Math.max(...ys)];
  let pts = [];
  for (let guard = 0; pts.length < n && guard < 5000; guard++) {
    let p;
    if (style.core) { // dense core: points pulled toward the middle
      const a = r() * Math.PI * 2, rr = Math.pow(r(), 1.6) * Math.max(box[2] - box[0], box[3] - box[1]) / 2;
      p = [rr * Math.cos(a), rr * Math.sin(a)];
    } else p = [box[0] + r() * (box[2] - box[0]), box[1] + r() * (box[3] - box[1])];
    if (pointIn(p, O) && pts.every((q) => Math.hypot(q[0] - p[0], q[1] - p[1]) > 8)) pts.push(p);
  }
  if (pts.length < n) return null;
  const big = 4 * R;
  let cells = [];
  const iters = style.relax;
  for (let iter = 0; iter <= iters; iter++) {
    const vor = Delaunay.from(pts).voronoi([-big, -big, big, big]);
    cells = pts.map((_, i) => {
      let cell = vor.cellPolygon(i).slice(0, -1);
      if (area(cell) < 0) cell.reverse();
      let c = clipPolygon(O, cell);
      if (c.length && area(c) < 0) c.reverse();
      return c;
    });
    if (iter < iters) pts = cells.map((c, i) => {
      if (c.length < 3) return pts[i];
      const cx = c.reduce((s, p) => s + p[0], 0) / c.length, cy = c.reduce((s, p) => s + p[1], 0) / c.length;
      // dense core: relax only partly, so the middle stays tighter
      const k = style.core ? 0.5 : 1;
      return [pts[i][0] + (cx - pts[i][0]) * k, pts[i][1] + (cy - pts[i][1]) * k];
    });
  }
  return cells.map((c) => c.map(bw));
}

/** The map is fine to play and to draw: blocks big enough and simple, one outer loop. */
function mapOk(m, n) {
  if (m.blocks.length !== n) return false;
  const P = (i) => [m.points[i].x, m.points[i].y];
  const areas = m.blocks.map((b) => area(b.corners.map(P)));
  const mean = areas.reduce((s, x) => s + x, 0) / n;
  for (const [i, b] of m.blocks.entries()) {
    if (b.corners.length < 3 || new Set(b.corners).size !== b.corners.length) return false;
    const poly = b.corners.map(P);
    if (areas[i] < Math.max(1800, mean * 0.3) || selfCrossing(poly)) return false;
    // not too thin: area over the longest side
    let longest = 0;
    poly.forEach((p, k) => { const q = poly[(k + 1) % poly.length]; longest = Math.max(longest, Math.hypot(q[0] - p[0], q[1] - p[1])); });
    if (areas[i] / longest < 14) return false;
  }
  const count = borderCounts(m);
  for (const v of count.values()) if (v !== 1 && v !== 2) return false;
  // the edge of town is one simple loop
  const deg = new Map();
  for (const [k, v] of count) if (v === 1) for (const x of k.split("-")) deg.set(x, (deg.get(x) ?? 0) + 1);
  if ([...deg.values()].some((d) => d !== 2)) return false;
  // blocks connected
  const sides = m.blocks.map((b) => new Set(b.corners.map((a, i) => sideKey(a, b.corners[(i + 1) % b.corners.length]))));
  const seen = new Set([0]), q = [0];
  while (q.length) { const i = q.shift(); for (let j = 0; j < n; j++) if (!seen.has(j) && [...sides[i]].some((s2) => sides[j].has(s2))) { seen.add(j); q.push(j); } }
  return seen.size === n;
}

function buildMap(cells, reorder) {
  const key = (p) => `${Math.round(p[0])},${Math.round(p[1])}`;
  const index = new Map(); const points = [];
  const idOf = (p) => {
    const k = key(p);
    if (!index.has(k)) { index.set(k, points.length); points.push({ x: Math.round(p[0]), y: Math.round(p[1]) }); }
    return index.get(k);
  };
  let blocks = cells.map((c) => {
    const ids = [];
    for (const p of c) { const id = idOf(p); if (ids[ids.length - 1] !== id) ids.push(id); }
    if (ids.length > 1 && ids[0] === ids[ids.length - 1]) ids.pop();
    return { corners: ids };
  });
  if (reorder) blocks = neighborOrder(blocks);
  const segKeys = new Set(); const segments = [];
  for (const b of blocks) b.corners.forEach((a, i) => {
    const c = b.corners[(i + 1) % b.corners.length];
    const k = a < c ? `${a}-${c}` : `${c}-${a}`;
    if (!segKeys.has(k)) { segKeys.add(k); segments.push({ a: Math.min(a, c), b: Math.max(a, c), kind: "street", terrain: "ground" }); }
  });
  return { points, segments, blocks };
}

/** Which shape, block style and river a seed gets (all from the seed). */
export function designFor(seed) {
  const r = rng(seed * 31 + 7);
  const family = FAMILIES[Math.floor(r() * FAMILIES.length)];
  const style = { core: r() < 0.4, thin: family !== "grid" && r() < 0.25, relax: family === "grid" ? 8 : 2 + Math.floor(r() * 5) };
  let river = RIVERS[Math.floor(r() * RIVERS.length)];
  if (family === "twin") river = "across";
  if (family === "crescent" || family === "peninsula") river = r() < 0.5 ? "none" : river; // water is beside them already
  return { family, style, river };
}

export function generateMap(seed, n, { reorder = true } = {}) {
  const r = rng(seed);
  const want = designFor(seed);
  let m = null, design = want;
  // a few tries of the chosen design; then plainer styles; finally the classic round town
  for (let attempt = 0; attempt < 40 && !m; attempt++) {
    const d = attempt < 24 ? want : attempt < 34 ? { ...want, style: { core: false, thin: false, relax: 8 } } : { family: "round", style: { core: false, thin: false, relax: 8 }, river: want.river };
    const outline = outlineFor(d.family, r);
    const cells = makeCells(outline, n, r, d.style);
    if (!cells || cells.some((c) => c.length < 3)) continue;
    const cand = buildMap(cells, reorder);
    if (mapOk(cand, n)) { m = cand; design = d; }
  }
  if (!m) throw new Error(`no map for seed ${seed}`);
  // the river (its own random numbers, so the roads don't change)
  addRiver(m, rng(seed * 7919 + 13), design.river, design.family);
  // two bus routes across town, in random directions
  const a = r() * Math.PI;
  m.routes = [
    { name: "Crosstown", path: streetPath(m, toward(m, Math.cos(a), Math.sin(a)), toward(m, -Math.cos(a), -Math.sin(a))) },
    { name: "Shoreline", path: streetPath(m, toward(m, Math.cos(a + 1.6), Math.sin(a + 1.6)), toward(m, -Math.cos(a + 1.6), -Math.sin(a + 1.6))) },
  ];
  m.design = design;
  return m;
}

/** Number blocks so that neighbors get close numbers (Cuthill–McKee: breadth
first from a block with the fewest neighbors). The solver fills blocks in
number order, so this settles each block's neighborhood early. */
function neighborOrder(blocks) {
  const sides = blocks.map((b) => new Set(b.corners.map((a, i) => {
    const c = b.corners[(i + 1) % b.corners.length];
    return a < c ? `${a}-${c}` : `${c}-${a}`;
  })));
  const nbrs = blocks.map((_, i) => blocks.map((_, j) => j).filter((j) =>
    j !== i && [...sides[i]].some((s) => sides[j].has(s))));
  const order = [], seen = new Set();
  while (order.length < blocks.length) {
    const start = blocks.map((_, i) => i).filter((i) => !seen.has(i))
      .reduce((a, b) => (nbrs[b].length < nbrs[a].length ? b : a));
    const queue = [start]; seen.add(start);
    while (queue.length) {
      const i = queue.shift(); order.push(i);
      for (const j of [...nbrs[i]].sort((a, b) => nbrs[a].length - nbrs[b].length))
        if (!seen.has(j)) { seen.add(j); queue.push(j); }
    }
  }
  return order.map((i) => blocks[i]);
}

const sideKey = (a, b) => (a < b ? `${a}-${b}` : `${b}-${a}`);

/** How many blocks border each segment, by "a-b" key. */
function borderCounts(m) {
  const count = new Map();
  for (const b of m.blocks) b.corners.forEach((a, i) => {
    const k = sideKey(a, b.corners[(i + 1) % b.corners.length]);
    count.set(k, (count.get(k) ?? 0) + 1);
  });
  return count;
}

/** Mark the river: chains of interior segments between points on the edge of town.
Interior points of a chain are not on the edge, so a river always runs between two blocks.
Patterns: "across" (anywhere across town), "straight" (the straightest crossing),
"bend" (enters and leaves on nearby sides), "fork" (a crossing plus a branch), "none". */
function addRiver(m, r, pattern = "across", family = "round") {
  if (pattern === "none") return;
  const count = borderCounts(m);
  const interior = m.segments.filter((s) => count.get(sideKey(s.a, s.b)) === 2);
  const onEdge = new Set();
  for (const s of m.segments) if (count.get(sideKey(s.a, s.b)) === 1) { onEdge.add(s.a); onEdge.add(s.b); }
  const adj = new Map();
  for (const s of interior) {
    if (!adj.has(s.a)) adj.set(s.a, []); if (!adj.has(s.b)) adj.set(s.b, []);
    adj.get(s.a).push(s); adj.get(s.b).push(s);
  }
  const cx = m.points.reduce((s, p) => s + p.x, 0) / m.points.length, cy = m.points.reduce((s, p) => s + p.y, 0) / m.points.length;
  const angle = (i) => Math.atan2(m.points[i].y - cy, m.points[i].x - cx);
  const P = (i) => m.points[i];
  const chainsFrom = (a, blocked = new Set()) => {
    const prev = new Map([[a, null]]);
    const queue = [a];
    while (queue.length) {
      const u = queue.shift();
      if (u !== a && onEdge.has(u)) continue;
      for (const s of adj.get(u) ?? []) {
        const v = s.a === u ? s.b : s.a;
        if (!prev.has(v) && !blocked.has(v)) { prev.set(v, s); queue.push(v); }
      }
    }
    return prev;
  };
  const chainTo = (prev, a, b) => { const c = []; for (let v = b; v !== a; ) { const s = prev.get(v); c.push(s); v = s.a === v ? s.b : s.a; } return c; };
  const length = (c) => c.reduce((t, s) => t + Math.hypot(P(s.a).x - P(s.b).x, P(s.a).y - P(s.b).y), 0);
  const starts = [...onEdge].filter((i) => adj.has(i));
  const cands = [];
  for (const a of starts) {
    const prev = chainsFrom(a);
    for (const b of starts) {
      if (b <= a || !prev.has(b)) continue;
      const d = angDiff(angle(a), angle(b));
      const chain = chainTo(prev, a, b);
      const straight = Math.hypot(P(a).x - P(b).x, P(a).y - P(b).y);
      cands.push({ a, b, d, chain, wiggle: length(chain) / Math.max(1, straight) });
    }
  }
  // split blocks evenly (twin towns): how many blocks lie on each side
  const balance = (chain) => {
    const river = new Set(chain.map((s) => sideKey(s.a, s.b)));
    const sides = m.blocks.map((bl) => bl.corners.map((x, i) => sideKey(x, bl.corners[(i + 1) % bl.corners.length])));
    const seen = new Set([0]), q = [0];
    while (q.length) { const i = q.shift(); for (let j = 0; j < m.blocks.length; j++) if (!seen.has(j) && sides[i].some((s2) => !river.has(s2) && sides[j].includes(s2))) { seen.add(j); q.push(j); } }
    return Math.abs(2 * seen.size - m.blocks.length);
  };
  let pool;
  if (pattern === "bend") pool = cands.filter((c) => c.d > Math.PI / 3 && c.d < (2 * Math.PI) / 3);
  else pool = cands.filter((c) => c.d >= (2 * Math.PI) / 3);
  // no street may leave the river at a shallow angle (it would run under the water)
  const landAt = new Map();
  for (const sg of m.segments) if (count.get(sideKey(sg.a, sg.b)) === 2 || count.get(sideKey(sg.a, sg.b)) === 1) for (const v of [sg.a, sg.b]) { if (!landAt.has(v)) landAt.set(v, []); landAt.get(v).push(sg); }
  const dirOf = (v, sg) => { const w = sg.a === v ? sg.b : sg.a; const dx = P(w).x - P(v).x, dy = P(w).y - P(v).y, L = Math.hypot(dx, dy) || 1; return [dx / L, dy / L]; };
  const cleanChain = (chain) => {
    const inChain = new Set(chain);
    for (const sg of chain) for (const v of [sg.a, sg.b]) {
      const rd = dirOf(v, sg);
      for (const o of landAt.get(v) ?? []) {
        if (inChain.has(o)) continue;
        // a street that meets the river must be long enough to reach dry land
        if (Math.hypot(P(o.a).x - P(o.b).x, P(o.a).y - P(o.b).y) < 16) return false;
        const od = dirOf(v, o);
        if (rd[0] * od[0] + rd[1] * od[1] > Math.cos((42 * Math.PI) / 180)) return false;
      }
    }
    return true;
  };
  const clean = pool.filter((c) => cleanChain(c.chain));
  if (clean.length) pool = clean;
  else if (cands.some((c) => cleanChain(c.chain))) pool = cands.filter((c) => cleanChain(c.chain));
  else return; // no river that keeps clear of the streets: this town has none
  if (!pool.length) pool = cands;
  // every river segment is a bridge site, and each one doubles the plans to check: keep rivers short
  const short = pool.filter((c) => c.chain.length <= (pattern === "fork" ? 4 : 5));
  if (short.length) pool = short;
  if (!pool.length) return;
  let pick;
  if (family === "twin") pick = pool.slice().sort((x, y) => balance(x.chain) - balance(y.chain) || x.wiggle - y.wiggle)[0];
  else if (pattern === "straight") pick = pool.slice().sort((x, y) => x.wiggle - y.wiggle)[0];
  else pick = pool[Math.floor(r() * pool.length)];
  for (const s of pick.chain) s.terrain = "stream";
  if (pattern === "fork") {
    // a branch from a point inside town on the river out to another edge point
    const riverPts = new Set(pick.chain.flatMap((s) => [s.a, s.b]));
    const inner = [...riverPts].filter((v) => !onEdge.has(v));
    for (const v of inner.sort(() => r() - 0.5)) {
      const prev = chainsFrom(v, new Set([...riverPts].filter((x) => x !== v)));
      const ends = starts.filter((b) => prev.has(b) && b !== pick.a && b !== pick.b && angDiff(angle(b), angle(pick.a)) > 0.8 && angDiff(angle(b), angle(pick.b)) > 0.8
        && chainTo(prev, v, b).length + pick.chain.length <= 6);
      if (!ends.length) continue;
      const b = ends[Math.floor(r() * ends.length)];
      for (const s of chainTo(prev, v, b)) s.terrain = "stream";
      break;
    }
  }
}

/** Shortest street path between intersections a and b (Dijkstra). A bus
crosses the river only by driving along a river segment (where a bridge can be
built): it never passes through a point on the river on two land segments.
River segments count double, so routes cross only when it is a real shortcut. */
export function streetPath(m, a, b) {
  const len = (s) => Math.floor(Math.hypot(m.points[s.a].x - m.points[s.b].x, m.points[s.a].y - m.points[s.b].y))
    * (s.terrain === "stream" ? 2 : 1);
  const onRiver = new Set();
  for (const s of m.segments) if (s.terrain === "stream") { onRiver.add(s.a); onRiver.add(s.b); }
  // State: point, and whether we arrived along a river segment (0/1).
  const key = (v, w) => 2 * v + w;
  const n2 = 2 * m.points.length;
  const dist = new Array(n2).fill(Infinity), prev = new Array(n2).fill(-1), done = new Set();
  dist[key(a, 1)] = 0; // the start may leave on land or water
  while (done.size < n2) {
    let u = -1;
    for (let i = 0; i < n2; i++) if (!done.has(i) && (u < 0 || dist[i] < dist[u])) u = i;
    if (u < 0 || dist[u] === Infinity) break;
    done.add(u);
    const pu = u >> 1, wet = u & 1;
    for (const s of m.segments) {
      const v = s.a === pu ? s.b : s.b === pu ? s.a : -1;
      if (v < 0) continue;
      const water = s.terrain === "stream" ? 1 : 0;
      // Land in, land out at a river point would cross the water without a bridge.
      if (onRiver.has(pu) && pu !== a && !wet && !water) continue;
      const k = key(v, water);
      if (dist[u] + len(s) < dist[k]) { dist[k] = dist[u] + len(s); prev[k] = u; }
    }
  }
  const end = dist[key(b, 0)] <= dist[key(b, 1)] ? key(b, 0) : key(b, 1);
  if (dist[end] === Infinity) return [a];
  const p = []; for (let k = end; k >= 0; k = prev[k]) p.unshift(k >> 1);
  return p;
}

/** The intersection farthest in direction (x, y). */
export function toward(m, x, y) {
  return m.points.reduce((best, p, i) =>
    (p.x * x + p.y * y > m.points[best].x * x + m.points[best].y * y ? i : best), 0);
}

if (process.argv[1] && process.argv[1].endsWith("genmap.mjs")) {
  const seed = Number(process.argv[2] ?? 7), n = Number(process.argv[3] ?? 7);
  const m = generateMap(seed, n);
  if (process.argv[4] === "--design") console.error(JSON.stringify(m.design));
  delete m.design;
  console.log(JSON.stringify(m));
}
