// Building models. Looks only: the kind and number of floors come from Lean.
// "Fewer, bigger, readable things": a few houses around a yard, one office
// tower, a row of shops, a park, a bar, or an open plot with a sign.
import * as THREE from "three";
import { GB, SHAPES, col, trs, w3, type P3 } from "./builder";
import { add, centroid, dist, mid, mul, norm, pointInPolygon, scaleAbout, segDist, sub, v2, inset, type V2 } from "./geom";
import { C } from "./palette";
import type { Building } from "./types";
import { Rng } from "./rng";

export const MAT_MAIN = new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.82, metalness: 0 });
export const MAT_GLOW = new THREE.MeshBasicMaterial({ vertexColors: true, toneMapped: false });

/** Height of a block's top surface. */
export const TILE_TOP = 0.16;
export const FLOOR = { housing: 0.52, office: 0.62, shop: 0.52, bar: 0.55 };

export interface Piece { obj: THREE.Group; delay: number }

export interface BuildCtx {
  poly: V2[];      // the block's plot outline, CCW
  center: V2;
  rng: Rng;
  keepClear?: V2;  // a spot to leave free (the subway entrance)
  fixed?: boolean;
  spots?: LifeSpots; // filled with benches and stroll spots for idle residents
}

/** The height of the tallest part of a building (for placing hearts above it). */
export function buildingHeight(b: Building): number {
  const s = Math.max(1, b.stories);
  switch (b.kind) {
    case "housing": return s * FLOOR.housing + 0.45;
    case "office": return s * FLOOR.office + 0.25;
    case "shop": return s * FLOOR.shop + 0.15;
    case "bar": return FLOOR.bar + 0.4;
    case "park": return 0.9;
    default: return 0.6;
  }
}

const HOUSE_WALLS = [C.butter, "#FFE9B8", "#FFD6A5", "#FFD3D9", "#FFF1CF"];
const HOUSE_ROOFS = [C.coral, "#FF9F8C", "#F47C6E", "#E0707E", "#F59A6B"];
const SHOP_WALLS = ["#7FDDB4", "#9FE6C8", "#6FD3B0"];
const white = () => col(C.white);

// ---------- frames ----------

/** A rectangle facing direction n (its "front"), centered at p. Corners CCW. */
function rect(p: V2, n: V2, w: number, d: number): V2[] {
  const a = v2(n.y, -n.x);
  const hw = w / 2, hd = d / 2;
  return [
    add(add(p, mul(a, -hw)), mul(n, -hd)), add(add(p, mul(a, hw)), mul(n, -hd)),
    add(add(p, mul(a, hw)), mul(n, hd)), add(add(p, mul(a, -hw)), mul(n, hd)),
  ];
}

function outward(a: V2, b: V2): V2 { return norm(v2(b.y - a.y, a.x - b.x)); }

/** Polygon edges, longest first, with outward normals. */
function edges(poly: V2[]) {
  return poly.map((a, i) => {
    const b = poly[(i + 1) % poly.length];
    return { a, b, m: mid(a, b), len: dist(a, b), n: outward(a, b) };
  }).sort((x, y) => y.len - x.len);
}

function inradius(poly: V2[], c: V2): number {
  let r = Infinity;
  for (let i = 0; i < poly.length; i++) r = Math.min(r, segDist(c, poly[i], poly[(i + 1) % poly.length]));
  return r;
}

function group(m: GB, g: GB | null, at: V2, y = TILE_TOP): THREE.Group {
  const grp = new THREE.Group();
  const o: P3 = [at.x, y, -at.y];
  grp.position.set(o[0], o[1], o[2]);
  if (!m.empty) {
    const mesh = new THREE.Mesh(m.build(o), MAT_MAIN);
    mesh.castShadow = true; mesh.receiveShadow = true;
    grp.add(mesh);
  }
  if (g && !g.empty) grp.add(new THREE.Mesh(g.build(o), MAT_GLOW));
  return grp;
}

/** A rectangle painted on a wall a→b (fractions t0..t1, heights h0..h1). */
function wallPatch(m: GB, a: V2, b: V2, t0: number, t1: number, h0: number, h1: number, c: THREE.Color, off = 0.012) {
  const n = outward(a, b);
  const o = mul(n, off);
  const p0 = add(add(a, mul(sub(b, a), t0)), o), p1 = add(add(a, mul(sub(b, a), t1)), o);
  m.quad(w3(p0, h0), w3(p1, h0), w3(p1, h1), w3(p0, h1), c, [n.x, 0, -n.y]);
}

/** Chunky framed windows along every wall of a footprint, for one floor. */
function windows(m: GB, F: V2[], y: number, fh: number, glass: THREE.Color, spacing: number, frontDoor = -1) {
  for (let e = 0; e < F.length; e++) {
    const a = F[e], b = F[(e + 1) % F.length];
    const L = dist(a, b);
    const n = Math.max(1, Math.round(L / spacing));
    for (let j = 0; j < n; j++) {
      const t = (j + 0.5) / n;
      const hw = Math.min(0.11, (L / n) * 0.3) / L;
      if (e === frontDoor && j === Math.floor(n / 2)) {
        wallPatch(m, a, b, t - 0.1 / L, t + 0.1 / L, y, y + fh * 0.62, col("#C9705F"), 0.014);
        wallPatch(m, a, b, t - 0.13 / L, t + 0.13 / L, y + fh * 0.62, y + fh * 0.68, white(), 0.016);
        continue;
      }
      wallPatch(m, a, b, t - hw - 0.03 / L, t + hw + 0.03 / L, y + fh * 0.3 - 0.03, y + fh * 0.72 + 0.03, white(), 0.01);
      wallPatch(m, a, b, t - hw, t + hw, y + fh * 0.3, y + fh * 0.72, glass, 0.016);
    }
  }
}

function pitchedRoof(m: GB, F: V2[], c: V2, y: number, H: number, roof: THREE.Color, gable: THREE.Color) {
  let [a, b, cc, d] = F;
  if (dist(mid(a, d), mid(b, cc)) < dist(mid(a, b), mid(cc, d))) [a, b, cc, d] = [b, cc, d, a];
  const [A, B, Cc, D] = scaleAbout([a, b, cc, d], c, 1.16);
  const r1 = mid(A, D), r2 = mid(B, Cc);
  const ye = y - 0.06, yr = y + H;
  const hint = (p: V2): P3 => [p.x - c.x, 1.2, -(p.y - c.y)];
  // thick roof slabs: top face, plus a white fascia along the eaves
  m.quad(w3(A, ye), w3(B, ye), w3(r2, yr), w3(r1, yr), roof, hint(mid(A, B)));
  m.quad(w3(Cc, ye), w3(D, ye), w3(r1, yr), w3(r2, yr), roof, hint(mid(Cc, D)));
  m.quad(w3(A, ye), w3(B, ye), w3(B, ye - 0.06), w3(A, ye - 0.06), white(), hint(mid(A, B)));
  m.quad(w3(Cc, ye), w3(D, ye), w3(D, ye - 0.06), w3(Cc, ye - 0.06), white(), hint(mid(Cc, D)));
  m.quad(w3(A, ye - 0.06), w3(B, ye - 0.06), w3(B, ye), w3(A, ye), white(), [0, -1, 0]);
  const o1 = outward(d, a), o2 = outward(b, cc);
  m.tri(w3(d, y), w3(a, y), w3(mid(a, d), yr), gable, [o1.x, 0, -o1.y]);
  m.tri(w3(b, y), w3(cc, y), w3(mid(b, cc), yr), gable, [o2.x, 0, -o2.y]);
}

/** A hipped roof: four slopes, a short ridge along the longer side. */
function hipRoof(m: GB, F: V2[], c: V2, y: number, H: number, roof: THREE.Color) {
  let [a, b, cc, d] = F;
  if (dist(mid(a, d), mid(b, cc)) < dist(mid(a, b), mid(cc, d))) [a, b, cc, d] = [b, cc, d, a];
  const [A, B, Cc, D] = scaleAbout([a, b, cc, d], c, 1.14);
  const m1 = mid(A, D), m2 = mid(B, Cc);
  const r1 = add(m1, mul(sub(m2, m1), 0.32)), r2 = add(m1, mul(sub(m2, m1), 0.68));
  const ye = y - 0.06, yr = y + H;
  const hint = (p: V2): P3 => [p.x - c.x, 1.2, -(p.y - c.y)];
  m.quad(w3(A, ye), w3(B, ye), w3(r2, yr), w3(r1, yr), roof, hint(mid(A, B)));
  m.quad(w3(Cc, ye), w3(D, ye), w3(r1, yr), w3(r2, yr), roof, hint(mid(Cc, D)));
  m.tri(w3(D, ye), w3(A, ye), w3(r1, yr), roof, hint(mid(D, A)));
  m.tri(w3(B, ye), w3(Cc, ye), w3(r2, yr), roof, hint(mid(B, Cc)));
  for (const [p0, p1] of [[A, B], [B, Cc], [Cc, D], [D, A]] as const) m.quad(w3(p0, ye), w3(p1, ye), w3(p1, ye - 0.06), w3(p0, ye - 0.06), white(), hint(mid(p0, p1)));
}

function flatRoof(m: GB, F: V2[], c: V2, y: number, cap: string) {
  m.prism(scaleAbout(F, c, 1.07), y, y + 0.09, white(), col(cap));
  m.prism(scaleAbout(F, c, 0.86), y + 0.09, y + 0.1, col(cap), col(cap));
}

export function tree(m: GB, p: V2, s: number, r: Rng, base = 0, leaf = C.leaf) {
  m.geom(SHAPES.cyl, trs(p.x, base + 0.16 * s, -p.y, 0.05 * s, 0.32 * s, 0.05 * s), col(C.trunk));
  m.geom(SHAPES.ball, trs(p.x, base + 0.5 * s, -p.y, 0.3 * s, 0.28 * s, 0.3 * s, r.range(0, 6)), col(leaf));
  m.geom(SHAPES.ball, trs(p.x + 0.08 * s, base + 0.7 * s, -(p.y - 0.04 * s), 0.18 * s, 0.17 * s, 0.18 * s), col(C.leafLight));
}

function lawn(m: GB, P: V2[], y: number, color = C.meadowDeep) {
  m.prism(P, y, y + 0.04, col(color), col(color));
}

// ---------- pieces ----------

/** One cute house: stacked floors with white bands, chunky windows, a door and a pitched roof. */
function house(p: V2, n: V2, w: number, d: number, floors: number, r: Rng): THREE.Group {
  const m = new GB();
  const F = rect(p, n, w, d);
  const wall = col(r.pick(HOUSE_WALLS));
  const fh = FLOOR.housing;
  m.prism(scaleAbout(F, p, 1.08), TILE_TOP, TILE_TOP + 0.06, white());
  const y0 = TILE_TOP + 0.06;
  for (let k = 0; k < floors; k++) {
    const y = y0 + k * fh;
    m.prism(F, y, y + fh, wall, null);
    if (k > 0) m.prism(scaleAbout(F, p, 1.045), y - 0.035, y + 0.035, white());
    windows(m, F, y, fh, col(C.window), 0.42, k === 0 ? 2 : -1);
  }
  const top = y0 + floors * fh;
  const roofC = col(r.pick(HOUSE_ROOFS)), H = Math.min(0.5, Math.min(w, d) * 0.5);
  if (r.chance(0.35)) hipRoof(m, F, p, top, H, roofC);
  else pitchedRoof(m, F, p, top, H, roofC, wall);
  // a little door canopy
  {
    const a = F[2], b = F[3], mdl = mid(a, b), along = norm(sub(b, a));
    const c0 = add(mdl, mul(along, -0.16)), c1 = add(mdl, mul(along, 0.16));
    const y = y0 + fh * 0.72;
    m.quad(w3(c0, y), w3(c1, y), w3(add(c1, mul(n, 0.16)), y - 0.06), w3(add(c0, mul(n, 0.16)), y - 0.06), roofC, [n.x, 1, -n.y]);
  }
  if (r.chance(0.55)) {
    const q = add(p, add(mul(v2(n.y, -n.x), w * 0.25), mul(n, -d * 0.15)));
    m.geom(SHAPES.box, trs(q.x, top + 0.32, -q.y, 0.12, 0.34, 0.12), white());
  }
  return group(m, null, p);
}

function tower(p: V2, n: V2, s: number, floors: number, r: Rng): THREE.Group {
  const m = new GB();
  const F = rect(p, n, s, s * 0.86);
  const fh = FLOOR.office;
  m.prism(scaleAbout(F, p, 1.08), TILE_TOP, TILE_TOP + 0.08, white());
  const y0 = TILE_TOP + 0.08;
  for (let k = 0; k < floors; k++) {
    const y = y0 + k * fh;
    m.prism(F, y, y + fh, col(C.sky), null);
    m.prism(scaleAbout(F, p, 1.04), y + fh - 0.05, y + fh, white());
    // a wide window band per floor, with mullions
    for (let e = 0; e < 4; e++) {
      const a = F[e], b = F[(e + 1) % 4];
      const L = dist(a, b);
      const cells = Math.max(2, Math.round(L / 0.36));
      for (let j = 0; j < cells; j++) wallPatch(m, a, b, (j + 0.14) / cells, (j + 0.86) / cells, y + 0.14, y + fh - 0.14, col("#5F86C8"), 0.014);
      if (k === 0 && e === 2) wallPatch(m, a, b, 0.4, 0.6, y, y + 0.36, col("#3E5E9A"), 0.02);
    }
  }
  const top = y0 + floors * fh;
  flatRoof(m, F, p, top, "#EAF3FC");
  // a rooftop sign facing the street, and an antenna
  const ang = Math.atan2(n.x, n.y);
  const q = add(p, mul(n, s * 0.2));
  m.geom(SHAPES.box, trs(q.x, top + 0.36, -q.y, s * 0.55, 0.3, 0.06, ang), col("#4F7FD0"));
  m.geom(SHAPES.box, trs(q.x + n.x * 0.035, top + 0.4, -(q.y + n.y * 0.035), s * 0.38, 0.06, 0.01, ang), white());
  m.geom(SHAPES.box, trs(q.x + n.x * 0.035, top + 0.3, -(q.y + n.y * 0.035), s * 0.26, 0.05, 0.01, ang), white());
  const an = add(p, mul(n, -s * 0.25));
  m.geom(SHAPES.cyl, trs(an.x, top + 0.45, -an.y, 0.02, 0.7, 0.02), col("#B8C7DD"));
  m.geom(SHAPES.ballLo, trs(an.x, top + 0.82, -an.y, 0.05, 0.05, 0.05), col(C.coral));
  void r;
  return group(m, null, p);
}

function shop(p: V2, n: V2, w: number, d: number, floors: number, r: Rng, awning: string): THREE.Group {
  const m = new GB();
  const F = rect(p, n, w, d);
  const fh = FLOOR.shop;
  const wallC = col(r.pick(SHOP_WALLS));
  m.prism(scaleAbout(F, p, 1.07), TILE_TOP, TILE_TOP + 0.06, white());
  const y0 = TILE_TOP + 0.06;
  for (let k = 0; k < floors; k++) {
    const y = y0 + k * fh;
    m.prism(F, y, y + fh, wallC, null);
    if (k > 0) m.prism(scaleAbout(F, p, 1.045), y - 0.035, y + 0.035, white());
    windows(m, F, y, fh, col(C.window), 0.42, k === 0 ? 2 : -1);
  }
  // shop front on the street side (edge 2 faces n)
  const a = F[2], b = F[3];
  wallPatch(m, a, b, 0.12, 0.88, y0 + 0.04, y0 + 0.34, col("#BFE6F5"), 0.014);
  wallPatch(m, a, b, 0.42, 0.58, y0, y0 + 0.36, col("#3F8C77"), 0.018);
  // striped awning
  const N = 6, h = y0 + 0.44;
  for (let j = 0; j < N; j++) {
    const p0 = add(a, mul(sub(b, a), 0.04 + (0.92 * j) / N)), p1 = add(a, mul(sub(b, a), 0.04 + (0.92 * (j + 1)) / N));
    m.quad(w3(add(p0, mul(n, 0.01)), h), w3(add(p1, mul(n, 0.01)), h), w3(add(p1, mul(n, 0.26)), h - 0.14), w3(add(p0, mul(n, 0.26)), h - 0.14),
      j % 2 ? white() : col(awning), [n.x, 1, -n.y]);
  }
  const top = y0 + floors * fh;
  if (r.chance(0.5)) flatRoof(m, F, p, top, "#BFEBD6");
  else pitchedRoof(m, F, p, top, Math.min(0.36, Math.min(w, d) * 0.4), col(r.pick(["#4FB08B", "#3E9C7C", awning])), wallC);
  // a hanging blade sign at the corner, in the awning color
  const bs = add(add(b, mul(n, 0.16)), mul(norm(sub(a, b)), 0.06));
  m.geom(SHAPES.cyl, trs(bs.x, y0 + 0.66, -bs.y, 0.012, 0.14, 0.012), col("#6B7A99"));
  m.geom(SHAPES.box, trs(bs.x, y0 + 0.56, -bs.y, 0.04, 0.18, 0.24, Math.atan2(n.x, n.y) + Math.PI / 2), col(awning));
  m.geom(SHAPES.ballLo, trs(bs.x, y0 + 0.56, -bs.y, 0.06, 0.06, 0.06), white());
  return group(m, null, p);
}

function bar(p: V2, n: V2, w: number, d: number): { m: GB; g: GB; top: number } {
  const m = new GB(), g = new GB();
  const F = rect(p, n, w, d);
  const fh = FLOOR.bar;
  m.prism(scaleAbout(F, p, 1.08), TILE_TOP, TILE_TOP + 0.06, white());
  const y0 = TILE_TOP + 0.06;
  m.prism(F, y0, y0 + fh, col(C.lavender), null);
  for (let e = 0; e < 4; e++) {
    const a = F[e], b = F[(e + 1) % 4];
    if (e === 2) {
      wallPatch(m, a, b, 0.42, 0.58, y0, y0 + 0.38, col("#7A5AA8"), 0.018);
      wallPatch(g, a, b, 0.14, 0.36, y0 + 0.16, y0 + 0.4, col(C.windowWarm), 0.016);
      wallPatch(g, a, b, 0.64, 0.86, y0 + 0.16, y0 + 0.4, col(C.windowWarm), 0.016);
    } else wallPatch(g, a, b, 0.25, 0.75, y0 + 0.16, y0 + 0.4, col(C.windowWarm), 0.016);
  }
  pitchedRoof(m, F, p, y0 + fh, 0.38, col("#9F86D6"), col(C.lavender));
  // a glowing cocktail-glass sign above the door
  const sg = add(mid(F[2], F[3]), mul(n, 0.12));
  const sy = y0 + fh + 0.12;
  g.geom(SHAPES.cone, new THREE.Matrix4().compose(new THREE.Vector3(sg.x, sy, -sg.y), new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(1, 0, 0), Math.PI), new THREE.Vector3(0.13, 0.16, 0.13)), col("#FFB3D0"));
  g.geom(SHAPES.cyl, trs(sg.x, sy - 0.15, -sg.y, 0.015, 0.14, 0.015), col("#FFB3D0"));
  g.geom(SHAPES.bulb, trs(sg.x + 0.05, sy + 0.05, -sg.y, 0.035, 0.035, 0.035), col("#B6F08A"));
  return { m, g, top: y0 + fh };
}

function bulbs(g: GB, a: V2, b: V2, ha: number, hb: number, r: Rng) {
  const n = Math.max(3, Math.round(dist(a, b) / 0.16));
  const cols = ["#FFE7A0", "#FFC7A8", "#FFB3D0"];
  for (let j = 0; j <= n; j++) {
    const t = j / n;
    const q = add(a, mul(sub(b, a), t));
    const h = ha + (hb - ha) * t - Math.sin(Math.PI * t) * 0.12;
    g.geom(SHAPES.bulb, trs(q.x, h, -q.y, 0.042, 0.042, 0.042), col(r.pick(cols)));
  }
}

function signPost(p: V2, n: V2, kind: "open" | "fixed"): THREE.Group {
  const m = new GB();
  const a = v2(n.y, -n.x);
  m.geom(SHAPES.cyl, trs(p.x, TILE_TOP + 0.3, -p.y, 0.03, 0.6, 0.03), col("#B98B6A"));
  // board
  const B = [add(p, mul(a, -0.24)), add(p, mul(a, 0.24))];
  const nn = mul(n, 0.03);
  const corners = [add(B[0], nn), add(B[1], nn), add(B[1], mul(nn, -1)), add(B[0], mul(nn, -1))];
  m.prism(corners, TILE_TOP + 0.42, TILE_TOP + 0.7, col(C.white));
  if (kind === "open") {
    // a big friendly "+"
    const c = add(p, mul(n, 0.035));
    const y = TILE_TOP + 0.56;
    const plus = (dx: number, dy: number, w: number, h: number) =>
      m.quad(w3(add(c, mul(a, dx - w)), y + dy - h), w3(add(c, mul(a, dx + w)), y + dy - h), w3(add(c, mul(a, dx + w)), y + dy + h), w3(add(c, mul(a, dx - w)), y + dy + h), col(C.leaf), [n.x, 0, -n.y]);
    plus(0, 0, 0.09, 0.025); plus(0, 0, 0.025, 0.09);
  } else {
    // a ribbon: "already built"
    const c = add(p, mul(n, 0.035));
    const y = TILE_TOP + 0.56;
    m.quad(w3(add(c, mul(a, -0.17)), y - 0.05), w3(add(c, mul(a, 0.17)), y - 0.05), w3(add(c, mul(a, 0.17)), y + 0.05), w3(add(c, mul(a, -0.17)), y + 0.05), col(C.coral), [n.x, 0, -n.y]);
    m.tri(w3(add(c, mul(a, -0.06)), y - 0.05), w3(add(c, mul(a, -0.12)), y - 0.17), w3(add(c, mul(a, -0.0)), y - 0.12), col(C.coral), [n.x, 0, -n.y]);
    m.tri(w3(add(c, mul(a, 0.06)), y - 0.05), w3(add(c, mul(a, 0.0)), y - 0.12), w3(add(c, mul(a, 0.12)), y - 0.17), col(C.coral), [n.x, 0, -n.y]);
  }
  return group(m, null, p);
}

/** Small dashes around the plot: an open lot waiting for a building. */
function dashedOutline(poly: V2[]): THREE.Group {
  const m = new GB();
  const P = inset(poly, 0.22);
  const y = TILE_TOP + 0.012;
  for (let i = 0; i < P.length; i++) {
    const a = P[i], b = P[(i + 1) % P.length];
    const L = dist(a, b), d = norm(sub(b, a)), nn = v2(-d.y * 0.06, d.x * 0.06);
    for (let s = 0.1; s < L - 0.1; s += 0.36) {
      const p0 = add(a, mul(d, s)), p1 = add(a, mul(d, Math.min(L - 0.05, s + 0.2)));
      m.quad(w3(add(p0, nn), y), w3(add(p1, nn), y), w3(sub(p1, nn), y), w3(sub(p0, nn), y), col("#FFFFFF"), [0, 1, 0]);
    }
  }
  return group(m, null, centroid(poly), 0);
}

// ---------- garden kit ----------

/** Places where residents can idle: benches to sit on and lawn spots to stroll around. */
export interface LifeSpots { benches: { p: V2; ang: number }[]; strolls: V2[] }

type Occ = { p: V2; rad: number }[];
const free = (occ: Occ, p: V2, pad: number) => occ.every((o) => dist(o.p, p) > o.rad + pad);

function bush(m: GB, p: V2, s: number, r: Rng) {
  m.geom(SHAPES.ball, trs(p.x, TILE_TOP + 0.1 * s, -p.y, 0.2 * s, 0.15 * s, 0.2 * s, r.range(0, 6)), col(r.pick(["#5DB866", "#6CC473", "#4FAE5E"])));
}

const FLOWERS = ["#FF8B7B", "#F7A8C8", "#FFE19A", "#FFFFFF", "#CDB6F3", "#FFB86B"];
function flowerBed(m: GB, p: V2, r: Rng) {
  const rx = r.range(0.18, 0.26), ry = r.range(0.12, 0.16), a = r.range(0, Math.PI);
  const pts: V2[] = [];
  for (let k = 0; k < 14; k++) {
    const t = (k / 14) * Math.PI * 2;
    const q = v2(Math.cos(t) * rx, Math.sin(t) * ry);
    pts.push(add(p, v2(q.x * Math.cos(a) - q.y * Math.sin(a), q.x * Math.sin(a) + q.y * Math.cos(a))));
  }
  m.prism(pts, TILE_TOP + 0.03, TILE_TOP + 0.08, col("#5DB866"), col("#6CC473"));
  const c = r.pick(FLOWERS), c2 = r.pick(FLOWERS);
  for (let k = 0; k < 9; k++) {
    const q = add(p, v2(r.range(-rx, rx) * 0.7, r.range(-ry, ry) * 0.7));
    m.geom(SHAPES.ballLo, trs(q.x, TILE_TOP + 0.11, -q.y, 0.045, 0.045, 0.045), col(k % 3 ? c : c2));
  }
}

function bench(m: GB, p: V2, ang: number) {
  const wood = col("#C99A72");
  m.geom(SHAPES.box, trs(p.x, TILE_TOP + 0.13, -p.y, 0.44, 0.05, 0.15, ang), wood);
  const back = add(p, v2(Math.sin(ang) * 0.07, Math.cos(ang) * 0.07));
  m.geom(SHAPES.box, trs(back.x, TILE_TOP + 0.24, -back.y, 0.44, 0.13, 0.035, ang), wood);
}

function planter(m: GB, p: V2, r: Rng) {
  m.geom(SHAPES.cyl, trs(p.x, TILE_TOP + 0.07, -p.y, 0.15, 0.14, 0.15), col("#E3DDEE"));
  tree(m, p, 0.7, r, TILE_TOP + 0.1);
}

function hedges(m: GB, area: V2[], occ: Occ, r: Rng, gapNear: V2[] = []) {
  const green = col("#4FAE5E");
  for (let i = 0; i < area.length; i++) {
    const a = area[i], b = area[(i + 1) % area.length];
    const L = dist(a, b), d = norm(sub(b, a));
    for (let s = 0.2; s < L - 0.2; s += 0.3) {
      const p = add(a, mul(d, s));
      if (!free(occ, p, 0.08) || gapNear.some((g) => dist(g, p) < 0.3)) continue;
      m.geom(SHAPES.box, trs(p.x, TILE_TOP + 0.1, -p.y, 0.32, 0.16, 0.13, Math.atan2(d.y, d.x)), green);
    }
  }
  void r;
}

type Item = "tree" | "bush" | "flowers" | "bench" | "planter" | "patch";
/** Scatter cozy things over the free parts of a block. */
function scatter(m: GB, area: V2[], occ: Occ, r: Rng, weights: [Item, number][], spots: LifeSpots | undefined, center: V2, step = 0.75) {
  const xs = area.map((p) => p.x), ys = area.map((p) => p.y);
  const inner = inset(area, 0.18);
  let benches = 0;
  const total = weights.reduce((s, w) => s + w[1], 0);
  for (let x = Math.min(...xs); x < Math.max(...xs); x += step) for (let y = Math.min(...ys); y < Math.max(...ys); y += step) {
    const p = v2(x + r.range(-0.2, 0.2), y + r.range(-0.2, 0.2));
    if (!pointInPolygon(p, inner) || !free(occ, p, 0.22)) continue;
    let pick = r.next() * (total + 0.6);
    let item: Item | null = null;
    for (const [it, w] of weights) { if (pick < w) { item = it; break; } pick -= w; }
    if (!item) { spots?.strolls.push(p); continue; }
    if (item === "bench" && benches >= 2) item = "bush";
    switch (item) {
      case "tree": tree(m, p, r.range(0.65, 0.95), r, TILE_TOP + 0.04); occ.push({ p, rad: 0.3 }); break;
      case "bush": bush(m, p, r.range(0.8, 1.2), r); occ.push({ p, rad: 0.2 }); break;
      case "flowers": flowerBed(m, p, r); occ.push({ p, rad: 0.3 }); break;
      case "planter": planter(m, p, r); occ.push({ p, rad: 0.3 }); break;
      case "patch": {
        const pts: V2[] = [];
        for (let k = 0; k < 12; k++) { const t = (k / 12) * Math.PI * 2; pts.push(add(p, v2(Math.cos(t) * 0.32, Math.sin(t) * 0.26))); }
        m.prism(pts, TILE_TOP, TILE_TOP + 0.04, col(C.meadowDeep), col(C.meadowDeep));
        bush(m, p, 0.7, r);
        occ.push({ p, rad: 0.32 });
        break;
      }
      case "bench": {
        const toC = norm(sub(center, p));
        const ang = Math.atan2(toC.x, toC.y);
        bench(m, p, ang);
        spots?.benches.push({ p, ang });
        benches++;
        occ.push({ p, rad: 0.3 });
        break;
      }
    }
  }
}

// ---------- layout per kind ----------

/** Build the pieces for one block. Each piece grows in on its own (staggered by `delay`). */
export function makeBuilding(b: Building, ctx: BuildCtx): Piece[] {
  const { poly, center, rng } = ctx;
  const floors = Math.max(1, b.stories);
  const out: Piece[] = [];
  const E = edges(poly);
  const r = inradius(poly, center);
  const occ: Occ = ctx.keepClear ? [{ p: ctx.keepClear, rad: 0.6 }] : [];
  const clearOf = (p: V2, rad: number) => free(occ, p, rad);
  const push = (obj: THREE.Group, delay: number) => out.push({ obj, delay });
  const area = inset(poly, 0.3); // inside the sidewalk ring
  const spots = ctx.spots;

  switch (b.kind) {
    case "housing": {
      // 3-5 houses facing the streets, each with a path; gardens fill the rest
      const fronts: V2[] = [];
      const g = new GB();
      lawn(g, area, TILE_TOP);
      const slots: { e: (typeof E)[number]; at: V2; w: number }[] = [];
      for (const e of E) {
        if (e.len < 1.1) continue;
        const two = e.len > 3.4;
        const w = Math.min(1.5, Math.max(0.95, e.len * (two ? 0.3 : 0.46)));
        const dir = norm(sub(e.b, e.a));
        if (two) { slots.push({ e, at: add(e.m, mul(dir, -e.len * 0.22)), w }, { e, at: add(e.m, mul(dir, e.len * 0.22)), w }); }
        else slots.push({ e, at: e.m, w });
      }
      for (const { e, at, w } of slots) {
        if (fronts.length >= 12) break;
        const d = Math.min(1.15, Math.max(0.85, r * 0.4));
        const p = add(at, mul(e.n, -(d / 2 + 0.42)));
        const rad = Math.hypot(w, d) / 2;
        if (!pointInPolygon(p, poly) || !clearOf(p, rad * 0.85)) continue;
        occ.push({ p, rad: rad * 0.95 });
        push(house(p, e.n, w, d, floors, rng), fronts.length * 0.08);
        // a little path from the front door to the sidewalk
        const f0 = add(p, mul(e.n, d / 2)), f1 = add(at, mul(e.n, -0.22));
        const pn = v2(-e.n.y * 0.1, e.n.x * 0.1);
        g.quad(w3(add(f0, pn), TILE_TOP + 0.045), w3(sub(f0, pn), TILE_TOP + 0.045), w3(sub(f1, pn), TILE_TOP + 0.045), w3(add(f1, pn), TILE_TOP + 0.045), col(C.plot), [0, 1, 0]);
        fronts.push(f1, add(p, mul(e.n, d / 2 + 0.1)));
      }
      hedges(g, area, occ, rng, fronts);
      scatter(g, area, occ, rng, [["tree", 0.35], ["bush", 0.15], ["flowers", 0.22], ["bench", 0.1]], spots, center);
      push(group(g, null, center), 0.3);
      break;
    }
    case "office": {
      const s = Math.min(2.2, Math.max(1.3, r * 0.9));
      push(tower(center, E[0].n, s, floors, rng), 0);
      occ.push({ p: center, rad: s * 0.72 });
      const g = new GB();
      lawn(g, area, TILE_TOP);
      // a paved plaza around the tower
      g.prism(rect(center, E[0].n, s * 1.7, s * 1.55), TILE_TOP, TILE_TOP + 0.05, col(C.plot), col(C.plot));
      occ.push({ p: center, rad: s * 0.95 });
      scatter(g, area, occ, rng, [["tree", 0.3], ["planter", 0.15], ["bench", 0.15], ["flowers", 0.18], ["bush", 0.1]], spots, center, 0.75);
      push(group(g, null, center), 0.3);
      break;
    }
    case "shop": {
      const e = E[0];
      const k = e.len > 3.2 ? 3 : 2;
      const total = Math.min(e.len * 0.82, k * 1.4);
      const w = total / k - 0.08;
      const d = Math.min(1.05, Math.max(0.85, r * 0.38));
      const along = norm(sub(e.b, e.a));
      const awnings = [C.coral, C.sky, "#F7A8C8"];
      for (let j = 0; j < k; j++) {
        const t = (j + 0.5) / k - 0.5;
        const p = add(add(e.m, mul(along, t * total)), mul(e.n, -(d / 2 + 0.36)));
        if (!clearOf(p, w / 2)) continue;
        occ.push({ p, rad: Math.hypot(w, d) / 2 * 0.95 });
        push(shop(p, e.n, w, d, floors, rng, awnings[j % 3]), j * 0.1);
      }
      const g = new GB();
      lawn(g, area, TILE_TOP);
      // a paved forecourt along the shop fronts
      g.prism(rect(add(e.m, mul(e.n, -0.62)), e.n, total + 0.3, 0.64), TILE_TOP, TILE_TOP + 0.05, col(C.plot), col(C.plot));
      for (let j = 0; j <= k; j++) {
        const t = j / k - 0.5;
        const q = add(add(e.m, mul(along, t * total)), mul(e.n, -0.5));
        if (pointInPolygon(q, area)) { planter(g, q, rng); }
      }
      scatter(g, area, occ, rng, [["tree", 0.3], ["bench", 0.18], ["flowers", 0.2], ["bush", 0.12]], spots, center, 0.75);
      push(group(g, null, center), 0.3);
      break;
    }
    case "bar": {
      const e = E[0];
      const p = center;
      const { m, g, top } = bar(p, e.n, Math.min(1.6, r * 0.8), Math.min(1.2, r * 0.6));
      occ.push({ p, rad: Math.min(1.6, r * 0.8) * 0.75 });
      const yard = new GB();
      lawn(yard, area, TILE_TOP);
      // patio with string lights to little poles
      const poles = poly.map((v) => add(v, mul(sub(center, v), 0.42))).filter((q) => pointInPolygon(q, poly) && clearOf(q, 0.2)).slice(0, 4);
      for (const q of poles) {
        m.geom(SHAPES.cyl, trs(q.x, TILE_TOP + 0.4, -q.y, 0.022, 0.8, 0.022), col("#8C7AA8"));
        bulbs(g, q, add(p, mul(sub(q, p), 0.25)), TILE_TOP + 0.78, top - 0.02, rng);
        occ.push({ p: q, rad: 0.15 });
      }
      for (let k = 0; k < 2; k++) {
        const q = add(add(p, mul(e.n, 0.95)), mul(v2(e.n.y, -e.n.x), (k - 0.5) * 0.9));
        if (!pointInPolygon(q, poly)) continue;
        m.geom(SHAPES.cyl, trs(q.x, TILE_TOP + 0.12, -q.y, 0.1, 0.05, 0.1), white());
        m.geom(SHAPES.cyl, trs(q.x, TILE_TOP + 0.26, -q.y, 0.015, 0.4, 0.015), white());
        m.geom(SHAPES.cone, trs(q.x, TILE_TOP + 0.48, -q.y, 0.26, 0.12, 0.26), col(k ? C.coral : C.lavender));
        occ.push({ p: q, rad: 0.3 });
        spots?.strolls.push(add(q, mul(e.n, 0.3)));
      }
      hedges(yard, area, occ, rng);
      scatter(yard, area, occ, rng, [["tree", 0.3], ["flowers", 0.3], ["bench", 0.15], ["bush", 0.15]], spots, center);
      push(group(m, g, p), 0);
      push(group(yard, null, center), 0.2);
      break;
    }
    case "park": {
      const m = new GB();
      lawn(m, inset(poly, 0.16), TILE_TOP);
      // pond
      const pc = add(center, v2(rng.range(-0.3, 0.3), rng.range(-0.3, 0.3)));
      const rx = Math.max(0.5, r * 0.36), ry = Math.max(0.35, r * 0.25);
      const pond: V2[] = [];
      for (let k = 0; k < 20; k++) { const t = (k / 20) * Math.PI * 2; pond.push(add(pc, v2(Math.cos(t) * rx, Math.sin(t) * ry))); }
      m.prism(scaleAbout(pond, pc, 1.12), TILE_TOP + 0.04, TILE_TOP + 0.05, col(C.sand), col(C.sand));
      m.prism(pond, TILE_TOP + 0.05, TILE_TOP + 0.055, col(C.water), col(C.water));
      occ.push({ p: pc, rad: Math.max(rx, ry) * 1.1 });
      // a ring path around the pond
      const ring = scaleAbout(pond, pc, 1.55), ring2 = scaleAbout(pond, pc, 1.35);
      for (let k = 0; k < ring.length; k++) {
        const k2 = (k + 1) % ring.length;
        m.quad(w3(ring[k], TILE_TOP + 0.045), w3(ring[k2], TILE_TOP + 0.045), w3(ring2[k2], TILE_TOP + 0.045), w3(ring2[k], TILE_TOP + 0.045), col("#F1E6CC"), [0, 1, 0]);
      }
      occ.push({ p: pc, rad: Math.max(rx, ry) * 1.6 });
      const bp = add(pc, v2(0, -(ry * 1.7 + 0.2)));
      if (pointInPolygon(bp, poly)) { bench(m, bp, 0); spots?.benches.push({ p: bp, ang: 0 }); occ.push({ p: bp, rad: 0.3 }); }
      scatter(m, inset(poly, 0.16), occ, rng, [["tree", 0.55], ["bush", 0.12], ["flowers", 0.15], ["bench", 0.1]], spots, center, 0.7);
      push(group(m, null, center), 0);
      break;
    }
    default: {
      // an open lot: fresh green plot, dashed outline, a "+" sign and a few wildflowers
      if (!ctx.fixed) push(dashedOutline(poly), 0);
      const e = E[0];
      const p = add(add(e.m, mul(e.n, -0.5)), mul(norm(sub(e.b, e.a)), Math.min(0.8, e.len * 0.25)));
      push(signPost(p, e.n, "open"), 0.05);
      const m = new GB();
      // soft grass tufts all over the plot
      const inner = inset(poly, 0.35);
      for (let k = 0; k < 70; k++) {
        const q = add(center, v2(rng.range(-r * 1.8, r * 1.8), rng.range(-r * 1.8, r * 1.8)));
        if (!pointInPolygon(q, inner) || dist(q, p) < 0.3) continue;
        const s = rng.range(0.7, 1.2);
        m.geom(SHAPES.cone, trs(q.x, TILE_TOP + 0.05 * s, -q.y, 0.07 * s, 0.12 * s, 0.07 * s, rng.range(0, 6)), col(rng.pick(["#8FD07A", "#7CC56B", "#A3DA88"])));
      }
      for (let k = 0; k < 14; k++) {
        const q = add(center, v2(rng.range(-r * 1.6, r * 1.6), rng.range(-r * 1.6, r * 1.6)));
        if (!pointInPolygon(q, inset(poly, 0.5)) || dist(q, p) < 0.5) continue;
        for (let j = 0; j < 5; j++) {
          const f = add(q, v2(rng.range(-0.12, 0.12), rng.range(-0.12, 0.12)));
          m.geom(SHAPES.ballLo, trs(f.x, TILE_TOP + 0.07, -f.y, 0.05, 0.05, 0.05), col(rng.pick(["#FFFFFF", "#FFE19A", "#F7A8C8", "#FF8B7B"])));
        }
        spots?.strolls.push(q);
      }
      if (!m.empty) push(group(m, null, center), 0.1);
    }
  }
  return out;
}

/** A sign post with a ribbon, marking a block that is already built. */
export function fixedMarker(poly: V2[], center: V2): THREE.Group {
  const E = edges(poly);
  const e = E[Math.min(1, E.length - 1)];
  const p = add(add(e.m, mul(e.n, -0.28)), mul(norm(sub(e.b, e.a)), Math.min(0.9, e.len * 0.32)));
  void center;
  return signPost(p, e.n, "fixed");
}

/** A small display model of a building kind, for the tray thumbnails (centered at the origin). */
export function thumbModel(kind: string): THREE.Group {
  const r = new Rng(7);
  const g = new THREE.Group();
  const base = new GB();
  const disc: V2[] = [];
  for (let k = 0; k < 28; k++) { const t = (k / 28) * Math.PI * 2; disc.push(v2(Math.cos(t) * 1.25, Math.sin(t) * 1.25)); }
  base.prism(disc, TILE_TOP - 0.16, TILE_TOP, col(C.meadow), col(C.plot));
  g.add(group(base, null, v2(0, 0)));
  const n = norm(v2(0.55, -1));
  switch (kind) {
    case "housing":
      g.add(house(v2(-0.05, 0.1), n, 1.25, 1.0, 2, r));
      { const m = new GB(); tree(m, v2(0.8, 0.55), 0.8, r, TILE_TOP); g.add(group(m, null, v2(0, 0))); }
      break;
    case "office": g.add(tower(v2(0, 0.1), n, 1.25, 3, r)); break;
    case "shop":
      g.add(shop(v2(-0.35, 0.35), n, 0.95, 0.85, 1, r, C.coral));
      g.add(shop(v2(0.45, 0.0), n, 0.95, 0.85, 1, r, C.sky));
      break;
    case "park": {
      const m = new GB();
      const pond: V2[] = [];
      for (let k = 0; k < 18; k++) { const t = (k / 18) * Math.PI * 2; pond.push(v2(0.25 + Math.cos(t) * 0.5, -0.25 + Math.sin(t) * 0.32)); }
      m.prism(pond, TILE_TOP, TILE_TOP + 0.01, col(C.water), col(C.water));
      tree(m, v2(-0.45, 0.35), 1.15, r, TILE_TOP);
      tree(m, v2(0.45, 0.55), 0.9, r, TILE_TOP);
      tree(m, v2(-0.6, -0.4), 0.8, r, TILE_TOP);
      g.add(group(m, null, v2(0, 0)));
      break;
    }
    case "bar": {
      const { m, g: glow, top } = bar(v2(0, 0.1), n, 1.2, 0.95);
      bulbs(glow, v2(-0.95, -0.55), v2(-0.3, -0.2), TILE_TOP + 0.75, top, r);
      m.geom(SHAPES.cyl, trs(-0.95, TILE_TOP + 0.38, 0.55, 0.02, 0.76, 0.02), col("#8C7AA8"));
      g.add(group(m, glow, v2(0, 0)));
      break;
    }
  }
  return g;
}

