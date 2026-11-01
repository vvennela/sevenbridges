// 2D geometry for drawing: polygons and the irregular quad grid inside blocks.
// Coordinates here are "plan" coordinates (x east, y north) in world units.
// World 3D is (x, height, -y). Looks only; no rule depends on this file.
import { Rng } from "./rng";

export interface V2 { x: number; y: number }

/** Map units (Lean's whole numbers) to world units. */
export const MAP_SCALE = 0.1;

export const v2 = (x: number, y: number): V2 => ({ x, y });
export const add = (a: V2, b: V2): V2 => ({ x: a.x + b.x, y: a.y + b.y });
export const sub = (a: V2, b: V2): V2 => ({ x: a.x - b.x, y: a.y - b.y });
export const mul = (a: V2, k: number): V2 => ({ x: a.x * k, y: a.y * k });
export const lerp2 = (a: V2, b: V2, t: number): V2 => ({ x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t });
export const mid = (a: V2, b: V2): V2 => lerp2(a, b, 0.5);
export const len = (a: V2): number => Math.hypot(a.x, a.y);
export const dist = (a: V2, b: V2): number => Math.hypot(a.x - b.x, a.y - b.y);
export const norm = (a: V2): V2 => { const l = len(a) || 1; return { x: a.x / l, y: a.y / l }; };
export const dot = (a: V2, b: V2): number => a.x * b.x + a.y * b.y;

export function signedArea(p: V2[]): number {
  let a = 0;
  for (let i = 0; i < p.length; i++) {
    const q = p[(i + 1) % p.length];
    a += p[i].x * q.y - q.x * p[i].y;
  }
  return a / 2;
}

/** The same polygon, counter-clockwise. */
export function ccw(p: V2[]): V2[] {
  return signedArea(p) < 0 ? [...p].reverse() : p;
}

export function centroid(p: V2[]): V2 {
  const a = signedArea(p);
  if (Math.abs(a) < 1e-9) return mul(p.reduce(add, v2(0, 0)), 1 / p.length);
  let cx = 0, cy = 0;
  for (let i = 0; i < p.length; i++) {
    const q = p[(i + 1) % p.length];
    const f = p[i].x * q.y - q.x * p[i].y;
    cx += (p[i].x + q.x) * f;
    cy += (p[i].y + q.y) * f;
  }
  return v2(cx / (6 * a), cy / (6 * a));
}

/** Is a CCW polygon convex (allowing nearly straight corners)? */
function isConvex(p: V2[]): boolean {
  const n = p.length;
  for (let i = 0; i < n; i++) {
    const a = p[i], b = p[(i + 1) % n], c = p[(i + 2) % n];
    const u = norm(sub(b, a)), w = norm(sub(c, b));
    // nearly straight corners (curving streets) still count as convex; clipping only trims a sliver
    if (u.x * w.y - u.y * w.x < -0.12) return false;
  }
  return true;
}

/** Inset a convex CCW polygon by clipping it with each edge moved inward by ds[i].
 * Unlike mitred offsets, short edges simply vanish instead of folding over. */
function clipInset(p: V2[], ds: number[]): V2[] {
  let poly = p.slice();
  const n = p.length;
  for (let i = 0; i < n; i++) {
    const a = p[i], b = p[(i + 1) % n];
    const e = norm(sub(b, a)), nin = v2(-e.y, e.x);
    const o = add(a, mul(nin, ds[i]));
    const side = (q: V2) => (q.x - o.x) * nin.x + (q.y - o.y) * nin.y;
    const out: V2[] = [];
    for (let k = 0; k < poly.length; k++) {
      const P = poly[k], Q = poly[(k + 1) % poly.length];
      const sp = side(P), sq = side(Q);
      if (sp >= 0) out.push(P);
      if ((sp >= 0) !== (sq >= 0)) out.push(add(P, mul(sub(Q, P), sp / (sp - sq))));
    }
    poly = out;
    if (poly.length < 3) return p.map(() => centroid(p));
  }
  return poly;
}

/** Move every edge of a CCW polygon inward by d (mitred corners, clamped). */
export function inset(p: V2[], d: number): V2[] {
  if (p.length > 3 && isConvex(p)) return clipInset(p, p.map(() => d));
  const n = p.length;
  return p.map((cur, i) => {
    const prev = p[(i - 1 + n) % n], next = p[(i + 1) % n];
    const e1 = norm(sub(cur, prev)), e2 = norm(sub(next, cur));
    const n1 = v2(-e1.y, e1.x), n2 = v2(-e2.y, e2.x);
    const bis = norm(add(n1, n2));
    const c = Math.max(dot(bis, n1), 0.35);
    return add(cur, mul(bis, d / c));
  });
}

/** Move each edge of a CCW polygon inward by its own distance ds[i] (edge i = p[i]→p[i+1]). */
export function insetEdges(p: V2[], ds: number[]): V2[] {
  if (p.length > 3 && isConvex(p)) return clipInset(p, ds);
  const n = p.length;
  return p.map((cur, i) => {
    const pi = (i - 1 + n) % n;
    const prev = p[pi], next = p[(i + 1) % n];
    const e1 = norm(sub(cur, prev)), e2 = norm(sub(next, cur));
    const n1 = v2(-e1.y, e1.x), n2 = v2(-e2.y, e2.x);
    const d1 = ds[pi], d2 = ds[i];
    // intersect the two offset lines: cur + n1*d1 + e1*s  and  cur + n2*d2 + e2*u
    const a1 = add(cur, mul(n1, d1)), a2 = add(cur, mul(n2, d2));
    const den = e1.x * e2.y - e1.y * e2.x;
    if (Math.abs(den) < 1e-4) return add(cur, mul(n2, d2));
    const s = ((a2.x - a1.x) * e2.y - (a2.y - a1.y) * e2.x) / den;
    const q = add(a1, mul(e1, s));
    // clamp very sharp corners
    return dist(q, cur) > 1.6 * Math.max(d1, d2) ? add(cur, mul(norm(add(n1, n2)), Math.max(d1, d2))) : q;
  });
}

/** Scale a polygon about a point. */
export function scaleAbout(p: V2[], c: V2, k: number): V2[] {
  return p.map((q) => add(c, mul(sub(q, c), k)));
}

export function pointInPolygon(q: V2, p: V2[]): boolean {
  let inside = false;
  for (let i = 0, j = p.length - 1; i < p.length; j = i++) {
    if ((p[i].y > q.y) !== (p[j].y > q.y) &&
        q.x < ((p[j].x - p[i].x) * (q.y - p[i].y)) / (p[j].y - p[i].y) + p[i].x) inside = !inside;
  }
  return inside;
}

/** One cell of a block's quad grid. */
export interface Cell {
  pts: V2[];        // 4 corners, CCW
  c: V2;            // center
  area: number;
  outEdge: number;  // index of the corner starting the cell's longest street-side edge, or -1
  edge: boolean;    // touches the block's outline
  depth: number;    // distance from center to the block's outline
}

/**
 * Fill a CCW polygon with irregular quads: fan it into triangles from its
 * center, split each triangle into 3 quads, subdivide, then relax the inner
 * points so the cells look organic.
 */
export function quadGrid(poly: V2[], rng: Rng, maxCellArea = 1.0): Cell[] {
  const verts: V2[] = [];
  const fixed: boolean[] = [];
  const edgeMid = new Map<string, number>();
  const outline = new Set<string>();
  const key = (a: number, b: number) => (a < b ? `${a},${b}` : `${b},${a}`);
  const addV = (p: V2, isFixed: boolean) => { verts.push(p); fixed.push(isFixed); return verts.length - 1; };
  const midOf = (a: number, b: number) => {
    const k = key(a, b);
    let m = edgeMid.get(k);
    if (m === undefined) {
      const onOutline = outline.has(k);
      m = addV(mid(verts[a], verts[b]), onOutline);
      edgeMid.set(k, m);
      if (onOutline) { outline.add(key(a, m)); outline.add(key(m, b)); }
    }
    return m;
  };

  const n = poly.length;
  const ring = poly.map((p) => addV(p, true));
  for (let i = 0; i < n; i++) outline.add(key(ring[i], ring[(i + 1) % n]));
  const c0 = centroid(poly);
  const center = addV(c0, false);

  let quads: number[][] = [];
  for (let i = 0; i < n; i++) {
    const a = ring[i], b = ring[(i + 1) % n];
    const g = addV(mul(add(add(verts[a], verts[b]), verts[center]), 1 / 3), false);
    const mab = midOf(a, b), mca = midOf(center, a), mcb = midOf(center, b);
    quads.push([a, mab, g, mca], [mab, b, mcb, g], [g, mcb, center, mca]);
  }

  const area = Math.abs(signedArea(poly));
  while (area / quads.length > maxCellArea && quads.length < 400) {
    const next: number[][] = [];
    for (const [a, b, c, d] of quads) {
      const ab = midOf(a, b), bc = midOf(b, c), cd = midOf(c, d), da = midOf(d, a);
      const m = addV(mul(add(add(verts[a], verts[b]), add(verts[c], verts[d])), 0.25), false);
      next.push([a, ab, m, da], [ab, b, bc, m], [m, bc, c, cd], [da, m, cd, d]);
    }
    quads = next;
  }

  // Relax: jitter inner points, then pull each toward the average of its neighbors.
  const nbrs: Set<number>[] = verts.map(() => new Set());
  for (const q of quads) for (let k = 0; k < 4; k++) { nbrs[q[k]].add(q[(k + 1) % 4]); nbrs[q[(k + 1) % 4]].add(q[k]); }
  const jitter = Math.sqrt(area / quads.length) * 0.22;
  for (let i = 0; i < verts.length; i++) if (!fixed[i]) verts[i] = add(verts[i], v2(rng.range(-jitter, jitter), rng.range(-jitter, jitter)));
  for (let it = 0; it < 8; it++) {
    const moved = verts.map((p, i) => {
      if (fixed[i] || nbrs[i].size === 0) return p;
      let s = v2(0, 0);
      for (const j of nbrs[i]) s = add(s, verts[j]);
      return lerp2(p, mul(s, 1 / nbrs[i].size), 0.5);
    });
    for (let i = 0; i < verts.length; i++) verts[i] = moved[i];
  }

  const outlineDist = (q: V2) => {
    let best = Infinity;
    for (let i = 0; i < n; i++) best = Math.min(best, segDist(q, poly[i], poly[(i + 1) % n]));
    return best;
  };
  return quads.map((q) => {
    const pts = q.map((i) => verts[i]);
    let outEdge = -1, best = 0;
    for (let k = 0; k < 4; k++) {
      if (outline.has(key(q[k], q[(k + 1) % 4]))) {
        const l = dist(pts[k], pts[(k + 1) % 4]);
        if (l > best) { best = l; outEdge = k; }
      }
    }
    const c = mul(pts.reduce(add, v2(0, 0)), 0.25);
    return { pts, c, area: Math.abs(signedArea(pts)), outEdge, edge: q.some((i) => fixed[i]), depth: outlineDist(c) };
  });
}

export function segDist(q: V2, a: V2, b: V2): number {
  const ab = sub(b, a);
  const t = Math.max(0, Math.min(1, dot(sub(q, a), ab) / (dot(ab, ab) || 1)));
  return dist(q, add(a, mul(ab, t)));
}

/** Points along a polyline, every `step` world units. */
export function polylineLength(p: V2[]): number {
  let l = 0;
  for (let i = 1; i < p.length; i++) l += dist(p[i - 1], p[i]);
  return l;
}

/** Point at distance s along a polyline (clamped), and its direction. */
export function along(p: V2[], s: number): { at: V2; dir: V2 } {
  for (let i = 1; i < p.length; i++) {
    const l = dist(p[i - 1], p[i]);
    if (s <= l || i === p.length - 1) {
      const t = l > 0 ? Math.max(0, Math.min(1, s / l)) : 0;
      return { at: lerp2(p[i - 1], p[i], t), dir: norm(sub(p[i], p[i - 1])) };
    }
    s -= l;
  }
  return { at: p[0], dir: v2(1, 0) };
}

/** A closed smooth curve through points (Catmull-Rom), `per` samples per span. */
export function smoothClosed(p: V2[], per = 6): V2[] {
  const out: V2[] = [];
  const n = p.length;
  for (let i = 0; i < n; i++) {
    const p0 = p[(i - 1 + n) % n], p1 = p[i], p2 = p[(i + 1) % n], p3 = p[(i + 2) % n];
    for (let k = 0; k < per; k++) {
      const t = k / per, t2 = t * t, t3 = t2 * t;
      const f = (a: number, b: number, c: number, d: number) =>
        0.5 * (2 * b + (-a + c) * t + (2 * a - 5 * b + 4 * c - d) * t2 + (-a + 3 * b - 3 * c + d) * t3);
      out.push(v2(f(p0.x, p1.x, p2.x, p3.x), f(p0.y, p1.y, p2.y, p3.y)));
    }
  }
  return out;
}
