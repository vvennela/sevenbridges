// The river through town ("stream" segments) and the bridges over it. Looks only:
// which segments are river and which bridges exist come from the puzzle and the solution.
import * as THREE from "three";
import { GB, SHAPES, col, trs, w3 } from "./builder";
import { add, dist, mul, norm, sub, v2, type V2 } from "./geom";
import { C } from "./palette";
import { Rng } from "./rng";

const WATER_W = 0.6;

export interface BridgeView { site: number; seg: number; a: V2; b: V2; ghost: THREE.Group; real: THREE.Group; hit: THREE.Mesh }

/** Water ribbons with sandy banks, reeds and stones along the river segments, and
 * a river that flows on out of town from any end that touches the ring road. */
export function buildRiver(scene: THREE.Scene, pts: V2[], segs: { a: number; b: number }[], river: number[], outerPts: Set<number>, center: V2, seed: number) {
  const rng = new Rng(seed ^ 0x51e7);
  const m = new GB(), deco = new GB();
  const ribbon = (a: V2, b: V2, w: number, y: number, c: THREE.Color, g: GB) => {
    const d = norm(sub(b, a)), n = v2(-d.y * w / 2, d.x * w / 2);
    g.quad(w3(add(a, n), y), w3(add(b, n), y), w3(sub(b, n), y), w3(sub(a, n), y), c, [0, 1, 0]);
  };
  const disc = (p: V2, r: number, y: number, c: THREE.Color, g: GB) => {
    const ring: ReturnType<typeof w3>[] = [];
    for (let k = 0; k < 16; k++) { const t = (k / 16) * Math.PI * 2; ring.push(w3(add(p, v2(Math.cos(t) * r, Math.sin(t) * r)), y)); }
    g.poly(ring, c, [0, 1, 0]);
  };
  const lines: [V2, V2][] = river.map((i) => [pts[segs[i].a], pts[segs[i].b]]);
  // ends on the ring road flow out into the meadow, curving gently
  const ends = new Map<number, number>();
  for (const i of river) for (const k of [segs[i].a, segs[i].b]) ends.set(k, (ends.get(k) ?? 0) + 1);
  for (const [k, n] of ends) {
    if (n !== 1 || !outerPts.has(k)) continue;
    let p = pts[k], ang = Math.atan2(p.y - center.y, p.x - center.x);
    for (let s = 0; s < 40; s++) {
      ang += Math.sin(s * 0.4 + k) * 0.08;
      const q = add(p, v2(Math.cos(ang) * 0.9, Math.sin(ang) * 0.9));
      lines.push([p, q]);
      p = q;
    }
  }
  for (const [a, b] of lines) {
    ribbon(a, b, WATER_W + 0.36, 0.024, col(C.sand), m);
    ribbon(a, b, WATER_W + 0.12, 0.027, col(C.shallows), m);
    ribbon(a, b, WATER_W, 0.03, col(C.water), m);
  }
  for (const [a, b] of lines) for (const p of [a, b]) {
    disc(p, (WATER_W + 0.36) / 2, 0.0241, col(C.sand), m);
    disc(p, (WATER_W + 0.12) / 2, 0.0271, col(C.shallows), m);
    disc(p, WATER_W / 2, 0.0301, col(C.water), m);
  }
  // reeds and stones along the banks
  for (const [a, b] of lines) {
    const L = dist(a, b), d = norm(sub(b, a)), n = v2(-d.y, d.x);
    for (let s = 0.2; s < L; s += 0.5) {
      if (!rng.chance(0.45)) continue;
      const side = rng.chance(0.5) ? 1 : -1;
      const p = add(add(a, mul(d, s)), mul(n, side * (WATER_W / 2 + 0.1)));
      if (rng.chance(0.6)) for (let j = 0; j < 3; j++) {
        const q = add(p, v2(rng.range(-0.05, 0.05), rng.range(-0.05, 0.05)));
        deco.geom(SHAPES.cyl, trs(q.x, 0.1, -q.y, 0.008, 0.18 + rng.range(0, 0.08), 0.008), col("#6AA84F"));
        deco.geom(SHAPES.cyl, trs(q.x, 0.21, -q.y, 0.016, 0.05, 0.016), col("#8A5A3B"));
      } else deco.geom(SHAPES.ball, trs(p.x, 0.04, -p.y, 0.06, 0.035, 0.05, rng.range(0, 6)), col("#B8B3AA"));
    }
  }
  const water = new THREE.Mesh(m.build(), new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.3 }));
  water.receiveShadow = true;
  const reeds = new THREE.Mesh(deco.build(), new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.8 }));
  reeds.castShadow = true;
  scene.add(water, reeds);
}

/** A cute arched stone bridge over segment a→b. `ghost`: a faint dashed outline (a site). */
export function bridgeMesh(a: V2, b: V2, ghost: boolean): THREE.Group {
  const grp = new THREE.Group();
  const mid = v2((a.x + b.x) / 2, (a.y + b.y) / 2);
  const d = norm(sub(b, a)), n = v2(-d.y, d.x);
  const span = WATER_W + 0.55, width = 0.5;
  // the bridge crosses the river: its length runs along n (from one bank to the other)
  const m = new GB();
  const stone = col("#D9CDB8"), rail = col("#F4EEE2"), deck = col("#C9A27E");
  const N = 10, rise = 0.16;
  const yAt = (t: number) => 0.06 + Math.sin(t * Math.PI) * rise;
  for (let k = 0; k < N; k++) {
    const t0 = k / N, t1 = (k + 1) / N;
    const p0 = add(mid, mul(n, (t0 - 0.5) * span)), p1 = add(mid, mul(n, (t1 - 0.5) * span));
    const w = mul(d, width / 2);
    if (ghost) {
      if (k % 2) continue;
      for (const s of [1, -1]) m.quad(w3(add(p0, mul(w, s)), yAt(t0) + 0.01), w3(add(p1, mul(w, s)), yAt(t1) + 0.01), w3(add(p1, mul(w, s * 0.8)), yAt(t1) + 0.01), w3(add(p0, mul(w, s * 0.8)), yAt(t0) + 0.01), col("#FFFFFF"), [0, 1, 0]);
      continue;
    }
    m.quad(w3(add(p0, w), yAt(t0)), w3(add(p1, w), yAt(t1)), w3(sub(p1, w), yAt(t1)), w3(sub(p0, w), yAt(t0)), deck, [0, 1, 0]);
    for (const s of [1, -1]) {
      const e0 = add(p0, mul(w, s)), e1 = add(p1, mul(w, s));
      m.quad(w3(e0, yAt(t0) - 0.08), w3(e1, yAt(t1) - 0.08), w3(e1, yAt(t1) + 0.1), w3(e0, yAt(t0) + 0.1), stone, [d.x * s, 0, -d.y * s]);
      m.quad(w3(e0, yAt(t0) + 0.1), w3(e1, yAt(t1) + 0.1), w3(add(e1, mul(d, -0.05 * s)), yAt(t1) + 0.1), w3(add(e0, mul(d, -0.05 * s)), yAt(t0) + 0.1), rail, [0, 1, 0]);
    }
  }
  if (!ghost) for (const t of [0, 1]) for (const s of [1, -1]) {
    const p = add(add(mid, mul(n, (t - 0.5) * span)), mul(d, s * width / 2));
    m.geom(SHAPES.box, trs(p.x, 0.12, -p.y, 0.08, 0.2, 0.08), rail);
    m.geom(SHAPES.bulb, trs(p.x, 0.24, -p.y, 0.035, 0.035, 0.035), rail);
  }
  const mat = ghost
    ? new THREE.MeshBasicMaterial({ vertexColors: true, transparent: true, opacity: 0.75, depthWrite: false })
    : new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.85 });
  const mesh = new THREE.Mesh(m.build(), mat);
  mesh.castShadow = !ghost;
  grp.add(mesh);
  return grp;
}
