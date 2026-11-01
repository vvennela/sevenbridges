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

export function generateMap(seed, n, { reorder = true } = {}) {
  const r = rng(seed);
  const R = 100;
  // 1. Wobbly outline: circle with smooth noise on the radius (3 sine waves).
  const ph = [r() * 6.28, r() * 6.28, r() * 6.28];
  const outline = [];
  const K = 24;
  for (let k = 0; k < K; k++) {
    const t = (k / K) * Math.PI * 2;
    const rad = R * (1 + 0.08 * Math.sin(2 * t + ph[0]) + 0.05 * Math.sin(3 * t + ph[1]) + 0.03 * Math.sin(5 * t + ph[2]));
    outline.push([rad * Math.cos(t), rad * Math.sin(t)]);
  }
  if (area(outline) < 0) outline.reverse();
  // 2. Seed points, spread out by Lloyd relaxation.
  let pts = [];
  while (pts.length < n) {
    const x = (r() * 2 - 1) * R * 0.8, y = (r() * 2 - 1) * R * 0.8;
    if (x * x + y * y < (R * 0.8) ** 2) pts.push([x, y]);
  }
  let cells = [];
  for (let iter = 0; iter <= 8; iter++) {
    const vor = Delaunay.from(pts).voronoi([-2 * R, -2 * R, 2 * R, 2 * R]);
    cells = pts.map((_, i) => {
      let cell = vor.cellPolygon(i).slice(0, -1);
      if (area(cell) < 0) cell.reverse();
      let c = clipPolygon(outline, cell);
      if (area(c) < 0) c.reverse();
      return c;
    });
    if (iter < 8) pts = cells.map((c) => {
      const cx = c.reduce((s, p) => s + p[0], 0) / c.length;
      const cy = c.reduce((s, p) => s + p[1], 0) / c.length;
      return [cx, cy];
    });
  }
  // 3. Round to whole numbers and build intersections, segments and blocks.
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
  const m = { points, segments, blocks };
  // 4. The river (its own random numbers, so the roads don't change).
  addRiver(m, rng(seed * 7919 + 13));
  // 5. Two bus routes across town, in random directions.
  const a = r() * Math.PI;
  m.routes = [
    { name: "Crosstown", path: streetPath(m, toward(m, Math.cos(a), Math.sin(a)), toward(m, -Math.cos(a), -Math.sin(a))) },
    { name: "Shoreline", path: streetPath(m, toward(m, Math.cos(a + 1.6), Math.sin(a + 1.6)), toward(m, -Math.cos(a + 1.6), -Math.sin(a + 1.6))) },
  ];
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

/** Mark a chain of interior segments, from an intersection on the edge of town
to one roughly across town, as the river. Interior points of the chain are not
on the edge, so the river cuts the town in two. */
function addRiver(m, r) {
  const count = borderCounts(m);
  const interior = m.segments.filter((s) => count.get(sideKey(s.a, s.b)) === 2);
  const onEdge = new Set();
  for (const s of m.segments) if (count.get(sideKey(s.a, s.b)) === 1) { onEdge.add(s.a); onEdge.add(s.b); }
  const adj = new Map();
  for (const s of interior) {
    if (!adj.has(s.a)) adj.set(s.a, []); if (!adj.has(s.b)) adj.set(s.b, []);
    adj.get(s.a).push(s); adj.get(s.b).push(s);
  }
  const angle = (i) => Math.atan2(m.points[i].y, m.points[i].x);
  const starts = [...onEdge].filter((i) => adj.has(i));
  const chains = [];
  for (const a of starts) {
    // Breadth-first search from a, through points not on the edge.
    const prev = new Map([[a, null]]);
    const queue = [a];
    while (queue.length) {
      const u = queue.shift();
      if (u !== a && onEdge.has(u)) continue;
      for (const s of adj.get(u) ?? []) {
        const v = s.a === u ? s.b : s.a;
        if (!prev.has(v)) { prev.set(v, s); queue.push(v); }
      }
    }
    for (const b of starts) {
      if (b <= a || !prev.has(b)) continue;
      let d = Math.abs(angle(a) - angle(b)); if (d > Math.PI) d = 2 * Math.PI - d;
      if (d < (2 * Math.PI) / 3) continue;
      const chain = [];
      for (let v = b; v !== a; ) { const s = prev.get(v); chain.push(s); v = s.a === v ? s.b : s.a; }
      chains.push(chain);
    }
  }
  if (!chains.length) return;
  const chain = chains[Math.floor(r() * chains.length)];
  for (const s of chain) s.terrain = "stream";
}

/** Shortest street path between intersections a and b (Dijkstra). A river
segment counts double: a bus can use it only over a bridge, so routes take it
only as a real shortcut. */
export function streetPath(m, a, b) {
  const len = (s) => Math.floor(Math.hypot(m.points[s.a].x - m.points[s.b].x, m.points[s.a].y - m.points[s.b].y))
    * (s.terrain === "stream" ? 2 : 1);
  const dist = m.points.map(() => Infinity), prev = m.points.map(() => -1), done = new Set();
  dist[a] = 0;
  while (done.size < m.points.length) {
    let u = -1;
    m.points.forEach((_, i) => { if (!done.has(i) && (u < 0 || dist[i] < dist[u])) u = i; });
    if (dist[u] === Infinity) break;
    done.add(u);
    for (const s of m.segments) {
      const v = s.a === u ? s.b : s.b === u ? s.a : -1;
      if (v >= 0 && dist[u] + len(s) < dist[v]) { dist[v] = dist[u] + len(s); prev[v] = u; }
    }
  }
  const p = []; for (let v = b; v >= 0; v = prev[v]) p.unshift(v);
  return p;
}

/** The intersection farthest in direction (x, y). */
export function toward(m, x, y) {
  return m.points.reduce((best, p, i) =>
    (p.x * x + p.y * y > m.points[best].x * x + m.points[best].y * y ? i : best), 0);
}

if (process.argv[1] && process.argv[1].endsWith("genmap.mjs")) {
  const seed = Number(process.argv[2] ?? 7), n = Number(process.argv[3] ?? 7);
  console.log(JSON.stringify(generateMap(seed, n)));
}
