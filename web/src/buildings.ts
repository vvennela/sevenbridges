// Building models. Looks only: the kind and number of floors come from Lean.
// "Fewer, bigger, readable things": a few houses around a yard, one office
// tower, a row of shops, a park, a bar, or an open plot with a sign.
import * as THREE from "three";
import { GB, SHAPES, col, trs, w3, type P3 } from "./builder";
import { add, centroid, dist, mid, mul, norm, pointInPolygon, scaleAbout, segDist, sub, v2, inset, type V2 } from "./geom";
import { C } from "./palette";
import type { Building } from "./types";
import { Rng } from "./rng";
import { alive } from "./ambient";

export const MAT_MAIN = alive(new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.82, metalness: 0 }), { wind: true, clouds: true, windows: true });
export const MAT_GLOW = new THREE.MeshBasicMaterial({ vertexColors: true, toneMapped: false });

/** Height of a block's top surface. */
export const TILE_TOP = 0.16;
export const FLOOR = { housing: 0.52, office: 0.62, shop: 0.52, bar: 0.55, food: 0.52 };

export interface Piece { obj: THREE.Group; delay: number }

export interface BuildCtx {
  poly: V2[];      // the block's plot outline, CCW
  center: V2;
  rng: Rng;
  keepClear?: V2;  // a spot to leave free (the subway entrance)
  /** Block number: picks the layout template, so neighboring blocks look different. */
  index?: number;
  /** A per-town number, so the same block number gets different templates in different towns. */
  townSalt?: number;
  fixed?: boolean;
  spots?: LifeSpots; // filled with benches and stroll spots for idle residents
}

/** The height of the tallest part of a building (for placing hearts above it). */
export function buildingHeight(b: Building): number {
  const s = Math.max(1, b.stories);
  switch (b.kind) {
    case "housing": return s * FLOOR.housing + 0.45;
    case "office": return s * FLOOR.office + (s >= 4 ? 0.7 : 0.25);
    case "food": return s * FLOOR.food + 0.45;
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
  const sw0 = m.sway, sb0 = m.swayBase;
  m.sway = 1 / Math.max(0.5, s); m.swayBase = base;
  m.geom(SHAPES.cyl, trs(p.x, base + 0.16 * s, -p.y, 0.05 * s, 0.32 * s, 0.05 * s), col(C.trunk));
  m.geom(SHAPES.ball, trs(p.x, base + 0.5 * s, -p.y, 0.3 * s, 0.28 * s, 0.3 * s, r.range(0, 6)), col(leaf));
  m.geom(SHAPES.ball, trs(p.x + 0.08 * s, base + 0.7 * s, -(p.y - 0.04 * s), 0.18 * s, 0.17 * s, 0.18 * s), col(C.leafLight));
  m.sway = sw0; m.swayBase = sb0;
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
  let top = y0 + floors * fh;
  flatRoof(m, F, p, top, "#EAF3FC");
  if (floors >= 4) {
    // tall towers: a glassy set-back crown with a white cap
    const G = scaleAbout(F, p, 0.62);
    m.prism(G, top + 0.1, top + 0.42, col("#7FA6DC"), null);
    for (let e = 0; e < 4; e++) wallPatch(m, G[e], G[(e + 1) % 4], 0.1, 0.9, top + 0.16, top + 0.36, col("#BFD8F6"), 0.012);
    flatRoof(m, G, p, top + 0.42, "#F4F8FD");
    top += 0.42;
  }
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
  m.sway = 0.6; m.swayBase = TILE_TOP;
  m.geom(SHAPES.ball, trs(p.x, TILE_TOP + 0.1 * s, -p.y, 0.2 * s, 0.15 * s, 0.2 * s, r.range(0, 6)), col(r.pick(["#5DB866", "#6CC473", "#4FAE5E"])));
  m.sway = 0;
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

// ---------- food, fences, lots and other V2 pieces ----------

const FOOD_WALLS = [C.peach, "#FFD8B8", "#FFE3C9"];

/** A café or a small restaurant: stacked floors, a scalloped awning, warm windows and a sign. */
function eatery(p: V2, n: V2, w: number, d: number, floors: number, r: Rng, style: "cafe" | "restaurant"): THREE.Group {
  const m = new GB(), g = new GB();
  const F = rect(p, n, w, d);
  const fh = FLOOR.food;
  const wall = col(style === "cafe" ? r.pick(FOOD_WALLS) : r.pick(["#F2A07E", C.terracotta, "#F4B08C"]));
  m.prism(scaleAbout(F, p, 1.07), TILE_TOP, TILE_TOP + 0.06, white());
  const y0 = TILE_TOP + 0.06;
  for (let k = 0; k < floors; k++) {
    const y = y0 + k * fh;
    m.prism(F, y, y + fh, wall, null);
    if (k > 0) { m.prism(scaleAbout(F, p, 1.045), y - 0.035, y + 0.035, white()); windows(m, F, y, fh, col(C.window), 0.42, -1); }
  }
  const a = F[2], b = F[3];
  // ground floor: a big warm window front and a door
  for (let e = 0; e < 4; e++) if (e !== 2) wallPatch(g, F[e], F[(e + 1) % 4], 0.25, 0.75, y0 + 0.14, y0 + 0.38, col(C.windowWarm), 0.014);
  wallPatch(g, a, b, 0.1, 0.4, y0 + 0.08, y0 + 0.38, col(C.windowWarm), 0.014);
  wallPatch(g, a, b, 0.6, 0.9, y0 + 0.08, y0 + 0.38, col(C.windowWarm), 0.014);
  wallPatch(m, a, b, 0.43, 0.57, y0, y0 + 0.36, col(style === "cafe" ? "#8A5A3B" : "#5E3A2E"), 0.018);
  // scalloped awning across the front
  const N = 7, h = y0 + 0.46, aw = style === "cafe" ? "#FF8B7B" : "#2F6F5E";
  for (let j = 0; j < N; j++) {
    const p0 = add(a, mul(sub(b, a), 0.03 + (0.94 * j) / N)), p1 = add(a, mul(sub(b, a), 0.03 + (0.94 * (j + 1)) / N));
    m.quad(w3(add(p0, mul(n, 0.01)), h), w3(add(p1, mul(n, 0.01)), h), w3(add(p1, mul(n, 0.3)), h - 0.15), w3(add(p0, mul(n, 0.3)), h - 0.15), j % 2 ? white() : col(aw), [n.x, 1, -n.y]);
    const pm = mid(p0, p1);
    m.tri(w3(add(p0, mul(n, 0.3)), h - 0.15), w3(add(p1, mul(n, 0.3)), h - 0.15), w3(add(pm, mul(n, 0.31)), h - 0.22), j % 2 ? white() : col(aw), [n.x, 0, -n.y]);
  }
  const top = y0 + floors * fh;
  if (style === "cafe") {
    pitchedRoof(m, F, p, top, Math.min(0.4, Math.min(w, d) * 0.42), col(r.pick(["#E98A6A", "#D9784F", C.coral])), wall);
    // a big coffee cup on a bracket over the door
    const q = add(add(mid(a, b), mul(n, 0.36)), mul(norm(sub(b, a)), 0.42));
    m.geom(SHAPES.cyl, trs(q.x, h + 0.02, -q.y, 0.012, 0.18, 0.012), col("#6B7A99"));
    m.geom(SHAPES.cyl, trs(q.x, h + 0.2, -q.y, 0.11, 0.16, 0.11), white());
    m.geom(SHAPES.cyl, trs(q.x, h + 0.285, -q.y, 0.1, 0.012, 0.1), col("#8A5A3B"));
    m.geom(SHAPES.ballLo, trs(q.x + n.y * 0.12, h + 0.2, -(q.y - n.x * 0.12), 0.05, 0.06, 0.05), white());
  } else {
    flatRoof(m, F, p, top, "#F7E3D2");
    // a rooftop sign board with a fork-and-knife mark
    const ang = Math.atan2(n.x, n.y);
    const q = add(p, mul(n, d * 0.25));
    m.geom(SHAPES.box, trs(q.x, top + 0.42, -q.y, w * 0.7, 0.42, 0.06, ang), col("#2F6F5E"));
    const f = add(q, mul(n, 0.04));
    const side = norm(sub(b, a));
    for (const [dx, wd] of [[-0.09, 0.025], [0.09, 0.03]] as const) {
      const c2 = add(f, mul(side, dx));
      m.geom(SHAPES.box, trs(c2.x, top + 0.42, -c2.y, wd, 0.28, 0.01, ang), white());
    }
    m.geom(SHAPES.ballLo, trs(f.x + side.x * 0.09, top + 0.52, -(f.y + side.y * 0.09), 0.035, 0.06, 0.012), white());
    for (const t of [0.15, 0.85]) {
      const q2 = add(add(a, mul(sub(b, a), t)), mul(n, 0.32));
      g.geom(SHAPES.bulb, trs(q2.x, h - 0.12, -q2.y, 0.05, 0.065, 0.05), col("#FFC86B"));
    }
  }
  return group(m, g, p);
}

/** A round café table with a parasol and chairs; chairs become seats for idle cats. */
function terraceTable(m: GB, p: V2, r: Rng, spots?: LifeSpots, parasol = true) {
  m.geom(SHAPES.cyl, trs(p.x, TILE_TOP + 0.16, -p.y, 0.14, 0.025, 0.14), white());
  m.geom(SHAPES.cyl, trs(p.x, TILE_TOP + 0.08, -p.y, 0.02, 0.16, 0.02), col("#6B7A99"));
  if (parasol) {
    m.geom(SHAPES.cyl, trs(p.x, TILE_TOP + 0.4, -p.y, 0.012, 0.5, 0.012), white());
    m.geom(SHAPES.cone, trs(p.x, TILE_TOP + 0.66, -p.y, 0.34, 0.14, 0.34), col(r.pick(["#FF8B7B", "#FFE19A", "#9FE2C6", "#F7A8C8"])));
  }
  const a0 = r.range(0, Math.PI);
  for (let k = 0; k < 2; k++) {
    const a = a0 + k * Math.PI;
    const q = add(p, v2(Math.cos(a) * 0.24, Math.sin(a) * 0.24));
    m.geom(SHAPES.box, trs(q.x, TILE_TOP + 0.09, -q.y, 0.1, 0.03, 0.1), col("#C99A72"));
    const ang = Math.atan2(-Math.cos(a), -Math.sin(a));
    spots?.benches.push({ p: q, ang });
  }
}

/** A row of white picket fence from a to b. */
function fence(m: GB, a: V2, b: V2) {
  const L = dist(a, b), d = norm(sub(b, a));
  const ang = Math.atan2(d.y, d.x);
  const mdl = mid(a, b);
  m.geom(SHAPES.box, trs(mdl.x, TILE_TOP + 0.13, -mdl.y, L, 0.025, 0.02, ang), white());
  for (let s = 0; s <= L; s += 0.12) {
    const q = add(a, mul(d, s));
    m.geom(SHAPES.box, trs(q.x, TILE_TOP + 0.1, -q.y, 0.03, 0.18, 0.02, ang), white());
  }
}

/** A small parking lot: gray asphalt, white bays and a few parked cars. */
function parkingLot(m: GB, p: V2, n: V2, w: number, d: number, r: Rng) {
  m.prism(rect(p, n, w, d), TILE_TOP, TILE_TOP + 0.03, col("#CFCBD9"), col("#D8D4E2"));
  const a = v2(n.y, -n.x);
  const bays = Math.max(2, Math.floor(w / 0.42));
  for (let j = 0; j <= bays; j++) {
    const q = add(p, mul(a, -w / 2 + (j * w) / bays));
    m.geom(SHAPES.box, trs(q.x, TILE_TOP + 0.035, -q.y, 0.02, 0.005, d * 0.8, Math.atan2(n.x, n.y)), white());
  }
  for (let j = 0; j < bays; j++) {
    if (r.chance(0.35)) continue;
    const q = add(p, mul(a, -w / 2 + ((j + 0.5) * w) / bays));
    const ang = Math.atan2(n.x, n.y);
    m.geom(SHAPES.box, trs(q.x, TILE_TOP + 0.1, -q.y, 0.2, 0.1, 0.34, ang), col(r.pick(["#FF8B7B", "#9CCAF4", "#9FE2C6", "#CDB6F3", "#FFE19A"])));
    m.geom(SHAPES.box, trs(q.x, TILE_TOP + 0.18, -q.y, 0.18, 0.08, 0.18, ang), col("#F4F8FF"));
  }
}

/** A tiered fountain on a round basin. */
function fountain(m: GB, g: GB, p: V2, s = 1) {
  const ring = (rad: number) => Array.from({ length: 18 }, (_, k) => add(p, v2(Math.cos((k / 18) * 6.283) * rad, Math.sin((k / 18) * 6.283) * rad)));
  m.prism(ring(0.62 * s), TILE_TOP, TILE_TOP + 0.13, white(), white());
  m.prism(ring(0.52 * s), TILE_TOP + 0.13, TILE_TOP + 0.135, col(C.water), col(C.water));
  m.geom(SHAPES.cyl, trs(p.x, TILE_TOP + 0.3, -p.y, 0.07 * s, 0.34, 0.07 * s), white());
  m.geom(SHAPES.cyl, trs(p.x, TILE_TOP + 0.46, -p.y, 0.24 * s, 0.05, 0.24 * s), white());
  g.geom(SHAPES.ball, trs(p.x, TILE_TOP + 0.56, -p.y, 0.08 * s, 0.14, 0.08 * s), col("#C9F0FA"));
}

/** A swing set, a slide and a sandbox. */
function playground(m: GB, p: V2, n: V2) {
  const a = v2(n.y, -n.x), ang = Math.atan2(n.x, n.y);
  m.prism(rect(p, n, 1.7, 1.1), TILE_TOP, TILE_TOP + 0.045, col(C.sand), col(C.sand));
  const s0 = add(p, mul(a, -0.45));
  for (const k of [-1, 1]) { const q = add(s0, mul(a, k * 0.3)); m.geom(SHAPES.cyl, trs(q.x, TILE_TOP + 0.25, -q.y, 0.02, 0.5, 0.02), col("#FF8B7B")); }
  m.geom(SHAPES.box, trs(s0.x, TILE_TOP + 0.5, -s0.y, 0.64, 0.03, 0.03, ang + Math.PI / 2), col("#FF8B7B"));
  for (const k of [-0.13, 0.13]) { const q = add(s0, mul(a, k)); m.geom(SHAPES.box, trs(q.x, TILE_TOP + 0.16, -q.y, 0.1, 0.02, 0.06, ang + Math.PI / 2), col("#FFE19A")); }
  const sl = add(p, mul(a, 0.4));
  m.geom(SHAPES.box, trs(sl.x, TILE_TOP + 0.18, -sl.y, 0.18, 0.36, 0.18, ang), col("#9CCAF4"));
  const sl2 = add(sl, mul(n, 0.26));
  const slide = new THREE.Matrix4().compose(new THREE.Vector3(sl2.x, TILE_TOP + 0.18, -sl2.y), new THREE.Quaternion().setFromEuler(new THREE.Euler(0.65, ang, 0, "YXZ")), new THREE.Vector3(0.14, 0.02, 0.5));
  m.geom(SHAPES.box, slide, col("#FFC83D"));
}

/** A striped market stall. */
function stall(m: GB, p: V2, n: V2, color: string) {
  const ang = Math.atan2(n.x, n.y);
  m.geom(SHAPES.box, trs(p.x, TILE_TOP + 0.12, -p.y, 0.5, 0.18, 0.26, ang), col("#C99A72"));
  for (let j = 0; j < 4; j++) {
    const q = add(p, mul(v2(n.y, -n.x), -0.19 + j * 0.125));
    m.geom(SHAPES.box, trs(q.x, TILE_TOP + 0.42, -q.y, 0.125, 0.03, 0.34, ang), j % 2 ? white() : col(color));
  }
  for (const k of [-1, 1]) { const q = add(p, mul(v2(n.y, -n.x), k * 0.23)); m.geom(SHAPES.cyl, trs(q.x, TILE_TOP + 0.3, -q.y, 0.012, 0.3, 0.012), white()); }
  const fruit = ["#FF8B7B", "#FFC83D", "#5FBF6A", "#F7A8C8"];
  for (let k = 0; k < 5; k++) { const q = add(p, mul(v2(n.y, -n.x), -0.18 + k * 0.09)); m.geom(SHAPES.ballLo, trs(q.x, TILE_TOP + 0.24, -q.y, 0.04, 0.04, 0.04), col(fruit[k % 4])); }
}

/** Vegetable rows (allotments). */
function veggies(m: GB, p: V2, n: V2, w: number, d: number) {
  m.prism(rect(p, n, w, d), TILE_TOP, TILE_TOP + 0.05, col("#B98B6A"), col("#A9805F"));
  const a = v2(n.y, -n.x);
  const rows = Math.max(2, Math.floor(w / 0.22));
  for (let j = 0; j < rows; j++) {
    const q0 = add(p, mul(a, -w / 2 + (j + 0.5) * (w / rows)));
    for (let s = -d / 2 + 0.1; s < d / 2 - 0.05; s += 0.14) {
      const q = add(q0, mul(n, s));
      m.geom(SHAPES.ballLo, trs(q.x, TILE_TOP + 0.08, -q.y, 0.05, 0.05, 0.05), col(j % 2 ? "#5FBF6A" : "#7FD07F"));
    }
  }
}

/** A small garden pool. */
function pool(m: GB, p: V2, n: V2) {
  m.prism(rect(p, n, 0.8, 0.5), TILE_TOP, TILE_TOP + 0.06, white(), white());
  m.prism(rect(p, n, 0.66, 0.36), TILE_TOP + 0.06, TILE_TOP + 0.062, col("#7FD3EA"), col("#7FD3EA"));
}

/** Pick a template for a block: the URL can force one (`?tpl=N`), else block number + seed. */
function pickTemplate(ctx: BuildCtx, n: number): number {
  const forced = new URLSearchParams(location.search).get("tpl");
  if (forced !== null && /^\d+$/.test(forced)) return Number(forced) % n;
  return ((ctx.index ?? 0) + (ctx.townSalt ?? 0)) % n;
}

// ---------- layout per kind ----------

/** Build the pieces for one block. Each piece grows in on its own (staggered by `delay`).
 * Every kind has a few layout templates; the block number and the town pick one, and the
 * block's own seed rotates and jitters it, so no two blocks look the same. Kind and floors
 * stay readable: every building on a block has the block's number of floors. */
export function makeBuilding(b: Building, ctx: BuildCtx): Piece[] {
  const { poly, center, rng } = ctx;
  const floors = Math.max(1, b.stories);
  const out: Piece[] = [];
  const E = edges(poly);
  const r = inradius(poly, center);
  const occ: Occ = ctx.keepClear ? [{ p: ctx.keepClear, rad: 0.6 }] : [];
  const clearOf = (p: V2, rad: number) => free(occ, p, rad);
  const push = (obj: THREE.Group, delay: number) => out.push({ obj, delay });
  /** Lawns, gardens, paths and small props: not a building footprint (the scene checks use this). */
  const pushYard = (obj: THREE.Group, delay: number) => { obj.userData.yard = true; out.push({ obj, delay }); };
  const area = inset(poly, 0.3); // inside the sidewalk ring
  const spots = ctx.spots;
  /** Does a w×d footprint at p facing n fit inside the block and clear of other things? */
  // buildings keep a little gap: their full half-diagonal must be clear of everything claimed
  const fits = (p: V2, n: V2, w: number, d: number, pad = 0.05) => rect(p, n, w + pad * 2, d + pad * 2).every((q) => pointInPolygon(q, area)) && clearOf(p, Math.hypot(w, d) / 2 * 1.02);
  const claim = (p: V2, w: number, d: number) => occ.push({ p, rad: Math.hypot(w, d) / 2 * 1.02 });
  /** A short paved path from a front door to the sidewalk. */
  const path = (g: GB, f0: V2, f1: V2, wid = 0.1) => {
    const dn = norm(sub(f1, f0)), pn = v2(-dn.y * wid, dn.x * wid);
    g.quad(w3(add(f0, pn), TILE_TOP + 0.045), w3(sub(f0, pn), TILE_TOP + 0.045), w3(sub(f1, pn), TILE_TOP + 0.045), w3(add(f1, pn), TILE_TOP + 0.045), col(C.plot), [0, 1, 0]);
  };
  const rot = rng.int(0, E.length - 1); // which edge a template treats as its "front"
  const ER = [...E.slice(rot), ...E.slice(0, rot)].filter((e) => e.len > 0.5);
  const front = E[rot % Math.min(2, E.length)];

  switch (b.kind) {
    case "housing": {
      const tpl = pickTemplate(ctx, 4);
      const g = new GB();
      lawn(g, area, TILE_TOP);
      let houses = 0;
      const addHouse = (p: V2, n: V2, w: number, d: number) => { claim(p, w, d); push(house(p, n, w, d, floors, rng), houses++ * 0.07); };
      const fronts: V2[] = [];
      if (tpl === 0 || tpl === 3) {
        // street fronts: houses face every street, each with a path; tpl 3 adds fenced yards
        for (const e of ER) {
          if (e.len < 1.1) continue;
          const k = e.len > 5 ? 3 : e.len > 3.2 ? 2 : 1;
          const w = Math.min(1.45, Math.max(0.95, (e.len / k) * rng.range(0.5, 0.62)));
          const d = Math.min(1.15, Math.max(0.85, r * 0.36)) * rng.range(0.9, 1.08);
          const dir = norm(sub(e.b, e.a));
          for (let j = 0; j < k; j++) {
            const at = add(e.m, mul(dir, ((j + 0.5) / k - 0.5) * e.len * 0.8 + rng.range(-0.15, 0.15)));
            const setback = tpl === 3 ? 0.75 : 0.42;
            const p = add(at, mul(e.n, -(d / 2 + setback)));
            if (!fits(p, e.n, w, d)) continue;
            addHouse(p, e.n, w, d);
            const f0 = add(p, mul(e.n, d / 2)), f1 = add(at, mul(e.n, -0.22));
            path(g, f0, f1);
            fronts.push(f1, add(p, mul(e.n, d / 2 + 0.1)));
            if (tpl === 3) {
              // a picket-fenced front yard with a gate gap
              const side = v2(e.n.y, -e.n.x);
              const yA = add(add(p, mul(e.n, d / 2 + 0.5)), mul(side, -w / 2 - 0.1)), yB = add(add(p, mul(e.n, d / 2 + 0.5)), mul(side, w / 2 + 0.1));
              const gate = add(p, mul(e.n, d / 2 + 0.5));
              // fences stay inside the plot (they would poke into the street at narrow corners)
              if (pointInPolygon(yA, area)) fence(g, yA, add(gate, mul(side, -0.14)));
              if (pointInPolygon(yB, area)) fence(g, add(gate, mul(side, 0.14)), yB);
              if (rng.chance(0.5)) flowerBed(g, add(add(p, mul(e.n, d / 2 + 0.25)), mul(side, w * 0.3)), rng);
            }
          }
        }
        if (tpl === 0) hedges(g, area, occ, rng, fronts);
        // the middle: allotments, a pool or a little green with a big tree
        const c2 = add(center, v2(rng.range(-0.3, 0.3), rng.range(-0.3, 0.3)));
        const pick = rng.int(0, 2);
        if (pick === 0 && fits(c2, front.n, 1.6, 1.0)) { veggies(g, c2, front.n, 1.6, 1.0); claim(c2, 1.6, 1.0); }
        else if (pick === 1 && fits(c2, front.n, 0.9, 0.6)) { pool(g, c2, front.n); claim(c2, 0.9, 0.6); }
        else if (clearOf(c2, 0.5)) { tree(g, c2, 1.5, rng, TILE_TOP); occ.push({ p: c2, rad: 0.5 }); }
      } else if (tpl === 1) {
        // a close: houses on a ring around a shared green, a lane in from the street
        const R = Math.max(1.4, r * rng.range(0.52, 0.6));
        const ringPts = Array.from({ length: 24 }, (_, k) => add(center, v2(Math.cos((k / 24) * 6.283) * (R - 0.95), Math.sin((k / 24) * 6.283) * (R - 0.95))));
        g.prism(ringPts, TILE_TOP, TILE_TOP + 0.045, col(C.plot), col(C.plot));
        const greenPts = ringPts.map((q) => add(center, mul(sub(q, center), 0.7)));
        g.prism(greenPts, TILE_TOP, TILE_TOP + 0.055, col("#9FD27F"), col("#9FD27F"));
        tree(g, center, 1.4, rng, TILE_TOP + 0.05);
        occ.push({ p: center, rad: R - 0.6 });
        const n0 = rng.int(6, 9), a0 = rng.range(0, 6.283);
        for (let k = 0; k < n0; k++) {
          const a = a0 + (k / n0) * 6.283;
          const p = add(center, v2(Math.cos(a) * R, Math.sin(a) * R));
          const n = norm(sub(center, p));
          const w = rng.range(1.0, 1.25), d = rng.range(0.85, 1.0);
          if (!fits(p, n, w, d)) continue;
          addHouse(p, n, w, d);
        }
        // the lane to the street
        const e = front;
        path(g, add(center, mul(norm(sub(e.m, center)), R - 0.9)), add(e.m, mul(e.n, -0.2)), 0.22);
        for (let k = 0; k < 4; k++) spots?.strolls.push(add(center, v2(Math.cos(k * 1.57 + 0.5) * (R - 0.95), Math.sin(k * 1.57 + 0.5) * (R - 0.95))));
      } else {
        // terraces: attached narrow houses in rows along the two longest streets, with back gardens
        for (const e of [ER[0], ER[1]].filter(Boolean)) {
          const dir = norm(sub(e.b, e.a));
          const wEach = rng.range(0.72, 0.85), d = 1.0;
          const k = Math.max(2, Math.floor((e.len * 0.78) / wEach));
          const start = -((k - 1) / 2) * wEach;
          for (let j = 0; j < k; j++) {
            const at = add(e.m, mul(dir, start + j * wEach));
            const p = add(at, mul(e.n, -(d / 2 + 0.38)));
            // terraced houses stand wall to wall: check only their own narrow width against what's claimed
            if (!rect(p, e.n, wEach - 0.02, d).every((q) => pointInPolygon(q, area)) || !clearOf(p, wEach * 0.45)) continue;
            occ.push({ p, rad: wEach * 0.5 }); push(house(p, e.n, wEach - 0.02, d, floors, rng), houses++ * 0.07);
            path(g, add(p, mul(e.n, d / 2)), add(at, mul(e.n, -0.22)), 0.07);
            // back garden fence
            const back = add(p, mul(e.n, -d / 2 - 0.7));
            const fa = add(back, mul(dir, -wEach / 2)), fb = add(back, mul(dir, wEach / 2));
            if (pointInPolygon(fa, area) && pointInPolygon(fb, area)) fence(g, fa, fb);
            if (j % 2 === 0 && rng.chance(0.7)) { const q = add(p, mul(e.n, -d / 2 - 0.35)); if (clearOf(q, 0.1)) bush(g, q, 0.8, rng); }
          }
        }
        // shared allotments in the middle
        const c2 = center;
        if (fits(c2, front.n, 1.8, 1.2)) { veggies(g, c2, front.n, 1.8, 1.2); claim(c2, 1.8, 1.2); }
      }
      // a block too odd for its template still gets its homes: one near the middle
      if (!houses) for (const [w, d] of [[1.2, 0.95], [1.0, 0.85], [0.85, 0.75]] as const) {
        const p = centroid(area);
        if (rect(p, front.n, w, d).every((q) => pointInPolygon(q, area))) { addHouse(p, front.n, w, d); break; }
      }
      scatter(g, area, occ, rng, [["tree", 0.35], ["bush", 0.15], ["flowers", 0.22], ["bench", 0.1]], spots, center);
      pushYard(group(g, null, center), 0.3);
      break;
    }
    case "office": {
      const tpl = pickTemplate(ctx, 3);
      const g = new GB();
      lawn(g, area, TILE_TOP);
      const n = front.n;
      /** The tower footprint (with its plinth) fits the plot. */
      const towerFits = (p: V2, s0: number) => rect(p, n, s0 * 1.1, s0 * 0.95).every((q) => pointInPolygon(q, area));
      const side0 = v2(n.y, -n.x);
      const twinS = Math.min(1.8, Math.max(1.15, r * 0.62));
      const tplUse = tpl === 1 && [-1, 1].every((k) => towerFits(add(center, mul(side0, k * twinS * 0.95)), twinS)) ? 1 : tpl === 1 ? 0 : tpl;
      if (tplUse === 1) {
        // twin towers on a shared plaza, a fountain between them
        const s = twinS;
        const side = side0;
        const gap = s * 0.95;
        g.prism(rect(center, n, s * 3.4, s * 1.7), TILE_TOP, TILE_TOP + 0.05, col(C.plot), col(C.plot));
        for (const k of [-1, 1]) { const p = add(center, mul(side, k * gap)); push(tower(p, n, s, floors, rng), k > 0 ? 0.1 : 0); occ.push({ p, rad: s * 0.72 }); }
        const fg = new GB();
        fountain(g, fg, add(center, mul(n, s * 0.45)), 0.75);
        occ.push({ p: center, rad: s * 1.6 });
        if (!fg.empty) pushYard(group(fg, null, center), 0.3);
      } else {
        // one tower; tpl 2 sets it toward the street and adds a parking lot behind
        let s = Math.min(2.2, Math.max(1.3, r * 0.9)) * (tplUse === 2 ? 0.85 : 1);
        let p = tplUse === 2 ? add(center, mul(n, Math.min(r * 0.35, 1.2))) : center;
        // a small or odd plot gets a slimmer tower in its middle
        if (!towerFits(p, s)) { p = centroid(area); while (s > 0.8 && !towerFits(p, s)) s *= 0.9; }
        if (towerFits(p, s)) push(tower(p, n, s, floors, rng), 0);
        occ.push({ p, rad: s * 0.72 });
        g.prism(rect(p, n, s * 1.7, s * 1.55), TILE_TOP, TILE_TOP + 0.05, col(C.plot), col(C.plot));
        occ.push({ p, rad: s * 0.95 });
        const lotP = add(p, mul(n, -(s * 0.78 + 0.75)));
        if (fits(lotP, n, s * 1.6, 1.0)) { parkingLot(g, lotP, n, s * 1.6, 1.0, rng); claim(lotP, s * 1.6, 1.0); }
      }
      scatter(g, area, occ, rng, [["tree", 0.3], ["planter", 0.15], ["bench", 0.15], ["flowers", 0.18], ["bush", 0.1]], spots, center, 0.75);
      pushYard(group(g, null, center), 0.3);
      break;
    }
    case "shop": {
      const tpl = pickTemplate(ctx, 3);
      const g = new GB();
      lawn(g, area, TILE_TOP);
      const awnings = [C.coral, C.sky, "#F7A8C8", C.butter];
      let j0 = 0;
      const row = (e: (typeof E)[number], k: number, inward = false) => {
        const total = Math.min(e.len * 0.8, k * 1.4);
        const w = total / k - 0.08;
        const d = Math.min(1.05, Math.max(0.85, r * 0.38));
        const along = norm(sub(e.b, e.a));
        const n = inward ? mul(e.n, -1) : e.n;
        for (let j = 0; j < k; j++) {
          const t = (j + 0.5) / k - 0.5;
          const p = add(add(e.m, mul(along, t * total)), mul(e.n, -(d / 2 + (inward ? 0.5 : 0.36))));
          if (!fits(p, n, w, d, 0)) continue;
          claim(p, w, d);
          push(shop(p, n, w, d, floors, rng, awnings[(j0++) % awnings.length]), j0 * 0.08);
        }
        if (!inward) {
          g.prism(rect(add(e.m, mul(e.n, -0.62)), e.n, total + 0.3, 0.64), TILE_TOP, TILE_TOP + 0.05, col(C.plot), col(C.plot));
          for (let j = 0; j <= k; j++) { const q = add(add(e.m, mul(along, (j / k - 0.5) * total)), mul(e.n, -0.5)); if (pointInPolygon(q, area) && clearOf(q, 0.1)) planter(g, q, rng); }
        }
      };
      if (tpl === 0) row(ER[0], ER[0].len > 3.2 ? 3 : 2);
      else if (tpl === 1) { row(ER[0], ER[0].len > 3.6 ? 3 : 2); if (ER[2]) row(ER[2], 2); }
      else {
        // a market square: shops face inward around stalls
        for (const e of ER.slice(0, 3)) row(e, 2, true);
        const sq = Array.from({ length: 20 }, (_, k) => add(center, v2(Math.cos((k / 20) * 6.283) * r * 0.42, Math.sin((k / 20) * 6.283) * r * 0.42)));
        g.prism(sq, TILE_TOP, TILE_TOP + 0.05, col(C.plot), col(C.plot));
        for (let k = 0; k < 4; k++) {
          const a = k * 1.57 + rng.range(0, 0.4);
          const q = add(center, v2(Math.cos(a) * r * 0.22, Math.sin(a) * r * 0.22));
          stall(g, q, norm(sub(q, center)), awnings[k]);
          occ.push({ p: q, rad: 0.35 });
          spots?.strolls.push(add(q, mul(norm(sub(q, center)), 0.45)));
        }
      }
      scatter(g, area, occ, rng, [["tree", 0.3], ["bench", 0.18], ["flowers", 0.2], ["bush", 0.12]], spots, center, 0.75);
      pushYard(group(g, null, center), 0.3);
      break;
    }
    case "food": {
      const tpl = pickTemplate(ctx, 3);
      const g = new GB();
      lawn(g, area, TILE_TOP);
      const d = 1.15;
      let placed = 0;
      const terrace = (e: (typeof E)[number], p: V2, w: number) => {
        // a paved terrace between the door and the street, with parasol tables
        const tp = add(p, mul(e.n, d / 2 + 0.45));
        g.prism(rect(tp, e.n, w + 0.5, 0.75), TILE_TOP, TILE_TOP + 0.05, col("#F3E3CF"), col("#F3E3CF"));
        const side = v2(e.n.y, -e.n.x);
        const nT = Math.max(2, Math.round(w / 0.6));
        for (let k = 0; k < nT; k++) { const q = add(tp, mul(side, ((k + 0.5) / nT - 0.5) * (w + 0.2))); terraceTable(g, q, rng, spots); occ.push({ p: q, rad: 0.3 }); }
        // planters at the terrace corners
        for (const k of [-1, 1]) { const q = add(tp, mul(side, k * (w / 2 + 0.35))); if (pointInPolygon(q, area) && clearOf(q, 0.1)) planter(g, q, rng); }
      };
      const place = (e: (typeof E)[number], style: "cafe" | "restaurant", w: number, at = e.m) => {
        const p = add(at, mul(e.n, -(d / 2 + 0.95)));
        if (!fits(p, e.n, w, d)) return false;
        claim(p, w, d);
        placed++;
        push(eatery(p, e.n, w, d, floors, rng, style), out.length * 0.08);
        terrace(e, p, w);
        return true;
      };
      // big blocks get a second place on another street
      const two = r > 2.6;
      if (tpl === 0) { place(ER[0], "cafe", 1.6); if (two && ER[2]) place(ER[2], "cafe", 1.3); }
      else if (tpl === 1) { place(ER[0], "restaurant", 1.9); if (two && ER[2]) place(ER[2], "cafe", 1.3); }
      else { place(ER[0], "cafe", 1.4); if (ER[1]) place(ER[1], "restaurant", 1.7); }
      // odd-shaped blocks: try every street, then smaller, so a food block always has its café
      if (!placed) for (const w of [1.4, 1.1, 0.9]) { for (const e of ER) if (place(e, "cafe", w)) break; if (placed) break; }
      if (!placed) { claim(center, 1.1, d); push(eatery(center, front.n, 1.1, d, floors, rng, "cafe"), 0); placed = 1; }
      // a garden with string lights in the back
      const back = add(center, mul(front.n, -r * 0.35));
      if (clearOf(back, 0.6)) { for (let k = 0; k < 2; k++) { const q = add(back, mul(v2(front.n.y, -front.n.x), (k - 0.5) * 0.7)); if (clearOf(q, 0.2)) { terraceTable(g, q, rng, spots, false); occ.push({ p: q, rad: 0.3 }); } } }
      scatter(g, area, occ, rng, [["tree", 0.32], ["flowers", 0.25], ["bush", 0.15], ["bench", 0.08]], spots, center, 0.75);
      pushYard(group(g, null, center), 0.3);
      break;
    }
    case "bar": {
      let tpl = pickTemplate(ctx, 2);
      let bw = Math.min(1.6, r * 0.8), bd = Math.min(1.2, r * 0.6);
      // the bar itself must fit the plot (small or odd plots get a smaller bar)
      for (let k = 0; k < 6 && !rect(center, E[0].n, bw * 1.1, bd * 1.1).every((q) => pointInPolygon(q, area)); k++) { bw *= 0.88; bd *= 0.88; }
      if (tpl === 1) {
        // the beer garden needs room in front of the bar; otherwise a patio
        const p1 = add(front.m, mul(front.n, -(bd / 2 + 0.5))), n1 = mul(front.n, -1);
        const gc1 = add(p1, mul(n1, bd / 2 + 1.1));
        if (!rect(gc1, n1, 2.7, 1.9).every((q) => pointInPolygon(q, area)) || !rect(p1, n1, bw, bd).every((q) => pointInPolygon(q, area))) tpl = 0;
      }
      const e = tpl === 0 ? E[0] : front;
      const p = tpl === 0 ? center : add(e.m, mul(e.n, -(bd / 2 + 0.5)));
      const n = tpl === 0 ? e.n : mul(e.n, -1); // the beer garden bar faces into its garden
      const { m, g, top } = bar(p, n, bw, bd);
      occ.push({ p, rad: bw * 0.75 });
      const yard = new GB();
      lawn(yard, area, TILE_TOP);
      if (tpl === 0) {
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
      } else {
        // a beer garden: long tables under rows of lights in front of the bar
        const gc = add(p, mul(n, bd / 2 + 1.1));
        yard.prism(rect(gc, n, 2.4, 1.6), TILE_TOP, TILE_TOP + 0.05, col("#F1E6CC"), col("#F1E6CC"));
        const side = v2(n.y, -n.x), ang = Math.atan2(side.x, side.y);
        for (const k of [-0.4, 0.4]) {
          const q = add(gc, mul(n, k));
          m.geom(SHAPES.box, trs(q.x, TILE_TOP + 0.16, -q.y, 0.24, 0.03, 1.6, ang), col("#C99A72"));
          for (const s2 of [-0.2, 0.2]) { const b2 = add(q, mul(n, s2)); m.geom(SHAPES.box, trs(b2.x, TILE_TOP + 0.09, -b2.y, 0.08, 0.03, 1.5, ang), col("#B98B6A")); }
          spots?.strolls.push(add(q, mul(side, 0.9)));
        }
        for (const k of [-1, 1]) {
          const q = add(add(gc, mul(side, k * 1.2)), mul(n, 0.8)), q2 = add(add(gc, mul(side, k * 1.2)), mul(n, -0.8));
          for (const pp of [q, q2]) m.geom(SHAPES.cyl, trs(pp.x, TILE_TOP + 0.4, -pp.y, 0.022, 0.8, 0.022), col("#8C7AA8"));
        }
        for (const s2 of [-0.8, 0, 0.8]) bulbs(g, add(add(gc, mul(side, -1.2)), mul(n, s2)), add(add(gc, mul(side, 1.2)), mul(n, s2)), TILE_TOP + 0.78, TILE_TOP + 0.78, rng);
        occ.push({ p: gc, rad: 1.3 });
      }
      hedges(yard, area, occ, rng);
      scatter(yard, area, occ, rng, [["tree", 0.3], ["flowers", 0.3], ["bench", 0.15], ["bush", 0.15]], spots, center);
      push(group(m, g, p), 0);
      pushYard(group(yard, null, center), 0.2);
      break;
    }
    case "park": {
      const tpl = pickTemplate(ctx, 3);
      const m = new GB(), glow = new GB();
      lawn(m, inset(poly, 0.16), TILE_TOP);
      if (tpl === 0) {
        // pond with a ring path
        const pc = add(center, v2(rng.range(-0.3, 0.3), rng.range(-0.3, 0.3)));
        const rx = Math.max(0.5, r * 0.36), ry = Math.max(0.35, r * 0.25);
        const pond: V2[] = [];
        for (let k = 0; k < 20; k++) { const t = (k / 20) * Math.PI * 2; pond.push(add(pc, v2(Math.cos(t) * rx, Math.sin(t) * ry))); }
        m.prism(scaleAbout(pond, pc, 1.12), TILE_TOP + 0.04, TILE_TOP + 0.05, col(C.sand), col(C.sand));
        m.prism(pond, TILE_TOP + 0.05, TILE_TOP + 0.055, col(C.water), col(C.water));
        const ring = scaleAbout(pond, pc, 1.55), ring2 = scaleAbout(pond, pc, 1.35);
        for (let k = 0; k < ring.length; k++) {
          const k2 = (k + 1) % ring.length;
          m.quad(w3(ring[k], TILE_TOP + 0.045), w3(ring[k2], TILE_TOP + 0.045), w3(ring2[k2], TILE_TOP + 0.045), w3(ring2[k], TILE_TOP + 0.045), col("#F1E6CC"), [0, 1, 0]);
        }
        occ.push({ p: pc, rad: Math.max(rx, ry) * 1.6 });
        const bp = add(pc, v2(0, -(ry * 1.7 + 0.2)));
        if (pointInPolygon(bp, poly)) { bench(m, bp, 0); spots?.benches.push({ p: bp, ang: 0 }); occ.push({ p: bp, rad: 0.3 }); }
      } else if (tpl === 1) {
        // a fountain plaza with paths out to every street
        for (const e of E) path(m, center, add(e.m, mul(e.n, -0.15)), 0.16);
        fountain(m, glow, center, 1.1);
        occ.push({ p: center, rad: 1.0 });
        for (let k = 0; k < 4; k++) {
          const a = k * 1.57 + 0.78;
          const q = add(center, v2(Math.cos(a) * 1.15, Math.sin(a) * 1.15));
          const ang = Math.atan2(-Math.cos(a), -Math.sin(a)) + Math.PI;
          bench(m, q, ang); spots?.benches.push({ p: q, ang }); occ.push({ p: q, rad: 0.3 });
        }
        for (const e of E) { const q = add(mid(center, e.m), mul(v2(e.n.y, -e.n.x), 0.45)); if (clearOf(q, 0.25)) { flowerBed(m, q, rng); occ.push({ p: q, rad: 0.3 }); } }
      } else {
        // a playground and a picnic meadow
        const pp = add(center, mul(front.n, Math.min(1.0, r * 0.3)));
        playground(m, pp, front.n);
        occ.push({ p: pp, rad: 1.0 });
        spots?.strolls.push(add(pp, mul(front.n, 0.7)), add(pp, mul(front.n, -0.7)));
        const pic = add(center, mul(front.n, -Math.min(1.2, r * 0.35)));
        if (clearOf(pic, 0.4)) {
          m.prism(rect(pic, front.n, 0.6, 0.45), TILE_TOP, TILE_TOP + 0.05, col("#FF8B7B"), col("#FF8B7B"));
          m.prism(rect(pic, front.n, 0.2, 0.45), TILE_TOP + 0.001, TILE_TOP + 0.052, white(), white());
          occ.push({ p: pic, rad: 0.4 });
          spots?.strolls.push(add(pic, v2(0.3, 0.1)));
        }
      }
      scatter(m, inset(poly, 0.16), occ, rng, [["tree", 0.55], ["bush", 0.12], ["flowers", 0.15], ["bench", 0.1]], spots, center, 0.7);
      pushYard(group(m, glow.empty ? null : glow, center), 0);
      break;
    }
    default: {
      // an open lot: fresh green plot, dashed outline, a "+" sign and a few wildflowers
      if (!ctx.fixed) pushYard(dashedOutline(poly), 0);
      const e = E[0];
      const p = add(add(e.m, mul(e.n, -0.5)), mul(norm(sub(e.b, e.a)), Math.min(0.8, e.len * 0.25)));
      pushYard(signPost(p, e.n, "open"), 0.05);
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
      if (!m.empty) pushYard(group(m, null, center), 0.1);
    }
  }
  // a block too odd for its template still shows its building (kind and floors stay readable)
  if (b.kind !== "empty" && b.kind !== "park" && !out.some((pc) => !pc.obj.userData.yard)) {
    const c = centroid(area), n = E[0].n;
    for (const k2 of [1, 0.8, 0.62]) {
      const w = 1.2 * k2, d = 0.95 * k2;
      if (!rect(c, n, w, d).every((q) => pointInPolygon(q, area))) continue;
      const g = b.kind === "housing" ? house(c, n, w, d, floors, rng)
        : b.kind === "office" ? tower(c, n, Math.min(w, d), floors, rng)
        : b.kind === "shop" ? shop(c, n, w, d, floors, rng, C.coral)
        : b.kind === "food" ? eatery(c, n, w, d, floors, rng, "cafe")
        : group(bar(c, n, w, d).m, bar(c, n, w, d).g, c);
      push(g, 0);
      break;
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
    case "food": {
      g.add(eatery(v2(-0.1, 0.25), n, 1.15, 0.85, 1, r, "cafe"));
      const m = new GB();
      terraceTable(m, add(v2(-0.1, 0.25), mul(n, 0.85)), r);
      terraceTable(m, add(add(v2(-0.1, 0.25), mul(n, 0.7)), v2(0.62, 0.3)), r);
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

