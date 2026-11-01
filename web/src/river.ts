// The river through town ("stream" segments) and the bridges over it. Looks only:
// which segments are river and which bridges exist come from the puzzle and the solution.
import * as THREE from "three";
import { GB, SHAPES, col, trs, w3 } from "./builder";
import { add, dist, mul, norm, sub, v2, type V2 } from "./geom";
import { C } from "./palette";
import { Rng } from "./rng";
import { BANK_LANE, BRIDGE_SPAN, BRIDGE_W, bridgeY, crossing } from "./transit";

const WATER_W = 1.5, BANK = 0.75;
/** Half the width of the river with its banks (blocks give way to it). */
export const RIVER_HALF = (WATER_W + BANK) / 2;

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
  const bent: [V2, V2][] = [];
  lines.forEach(([a, b], li) => {
    const d = norm(sub(b, a)), n = v2(-d.y, d.x), L = dist(a, b), K = Math.max(2, Math.round(L * 3));
    const amp = li < river.length ? Math.min(0.18, L * 0.04) : 0.25;
    const at = (t: number) => add(add(a, mul(d, t * L)), mul(n, Math.sin(t * Math.PI * 2) * amp));
    for (let k = 0; k < K; k++) bent.push([at(k / K), at((k + 1) / K)]);
  });
  for (const [a, b] of bent) {
    ribbon(a, b, WATER_W + BANK, 0.024, col(C.sand), m);
    ribbon(a, b, WATER_W + 0.3, 0.027, col(C.shallows), m);
    ribbon(a, b, WATER_W, 0.03, col(C.water), m);
  }
  for (const [a, b] of bent) for (const p of [a, b]) {
    disc(p, (WATER_W + BANK) / 2, 0.0241, col(C.sand), m);
    disc(p, (WATER_W + 0.3) / 2, 0.0271, col(C.shallows), m);
    disc(p, WATER_W / 2, 0.0301, col(C.water), m);
  }
  // lily pads and a few ducks on the water
  for (const [a, b] of bent) {
    if (!rng.chance(0.35)) continue;
    const d = norm(sub(b, a)), n = v2(-d.y, d.x);
    const p = add(mid2(a, b), mul(n, rng.range(-0.4, 0.4) * WATER_W));
    if (rng.chance(0.65)) for (let j = 0; j < 3; j++) {
      const q = add(p, v2(rng.range(-0.15, 0.15), rng.range(-0.15, 0.15)));
      disc(q, rng.range(0.05, 0.08), 0.034, col("#7CC27A"), deco);
      if (rng.chance(0.3)) deco.geom(SHAPES.bulb, trs(q.x, 0.045, -q.y, 0.025, 0.02, 0.025), col("#F7A8C8"));
    } else {
      // a little duck
      deco.geom(SHAPES.bulb, trs(p.x, 0.07, -p.y, 0.07, 0.05, 0.05, Math.atan2(d.x, d.y)), col("#FFFFFF"));
      const h = add(p, mul(d, 0.06));
      deco.geom(SHAPES.bulb, trs(h.x, 0.13, -h.y, 0.035, 0.035, 0.035), col("#FFFFFF"));
      const bk = add(h, mul(d, 0.035));
      deco.geom(SHAPES.bulb, trs(bk.x, 0.125, -bk.y, 0.018, 0.01, 0.018), col("#FFB347"));
    }
  }
  // reeds and stones along the banks
  for (const [a, b] of bent) {
    const L = dist(a, b), d = norm(sub(b, a)), n = v2(-d.y, d.x);
    for (let s = 0.1; s < L; s += 0.35) {
      if (!rng.chance(0.45)) continue;
      const side = rng.chance(0.5) ? 1 : -1;
      const p = add(add(a, mul(d, s)), mul(n, side * (WATER_W / 2 + 0.15)));
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
  if (ghost) {
    // a faint see-through copy of the real bridge
    const g = bridgeModel(a, b);
    g.traverse((o) => { if (o instanceof THREE.Mesh) { o.material = new THREE.MeshBasicMaterial({ color: 0xffffff, transparent: true, opacity: 0.18, depthWrite: false }); o.castShadow = false; } });
    return g;
  }
  return bridgeModel(a, b);
}

function bridgeModel(a: V2, b: V2): THREE.Group {
  const ghost = false;
  // the deck spans the river bank to bank (perpendicular to the water), arching over the middle
  const grp = new THREE.Group();
  const { mid, d, n } = crossing(a, b);
  const span = BRIDGE_SPAN, width = BRIDGE_W;
  const m = new GB();
  const stone = col("#D9CDB8"), rail = col("#F4EEE2"), deck = col("#C9A27E"), road = col(C.road);
  const N = 12;
  const w = mul(d, width / 2);
  for (let k = 0; k < N; k++) {
    const t0 = k / N, t1 = (k + 1) / N;
    const p0 = add(mid, mul(n, (t0 - 0.5) * span)), p1 = add(mid, mul(n, (t1 - 0.5) * span));
    if (ghost) {
      if (k % 2) continue;
      for (const s of [1, -1]) m.quad(w3(add(p0, mul(w, s)), bridgeY(t0) + 0.01), w3(add(p1, mul(w, s)), bridgeY(t1) + 0.01), w3(add(p1, mul(w, s * 0.75)), bridgeY(t1) + 0.01), w3(add(p0, mul(w, s * 0.75)), bridgeY(t0) + 0.01), col("#FFFFFF"), [0, 1, 0]);
      m.quad(w3(add(p0, mul(w, 0.1)), bridgeY(t0) + 0.01), w3(add(p1, mul(w, 0.1)), bridgeY(t1) + 0.01), w3(add(p1, mul(w, -0.1)), bridgeY(t1) + 0.01), w3(add(p0, mul(w, -0.1)), bridgeY(t0) + 0.01), col("#FFFFFF"), [0, 1, 0]);
      continue;
    }
    m.quad(w3(add(p0, w), bridgeY(t0)), w3(add(p1, w), bridgeY(t1)), w3(sub(p1, w), bridgeY(t1)), w3(sub(p0, w), bridgeY(t0)), deck, [0, 1, 0]);
    for (const s of [1, -1]) {
      const e0 = add(p0, mul(w, s)), e1 = add(p1, mul(w, s));
      m.quad(w3(e0, bridgeY(t0) - 0.1), w3(e1, bridgeY(t1) - 0.1), w3(e1, bridgeY(t1) + 0.1), w3(e0, bridgeY(t0) + 0.1), stone, [d.x * s, 0, -d.y * s]);
      m.quad(w3(e0, bridgeY(t0) + 0.1), w3(e1, bridgeY(t1) + 0.1), w3(add(e1, mul(d, -0.05 * s)), bridgeY(t1) + 0.1), w3(add(e0, mul(d, -0.05 * s)), bridgeY(t0) + 0.1), rail, [0, 1, 0]);
    }
  }
  if (!ghost) {
    // posts with round caps at the four corners
    for (const t of [0, 1]) for (const s of [1, -1]) {
      const p = add(add(mid, mul(n, (t - 0.5) * span)), mul(w, s));
      m.geom(SHAPES.box, trs(p.x, bridgeY(t) + 0.08, -p.y, 0.12, 0.26, 0.12), stone);
      // a lamp post at each corner
      m.geom(SHAPES.cyl, trs(p.x, bridgeY(t) + 0.45, -p.y, 0.022, 0.6, 0.022), col("#5B6478"));
      m.geom(SHAPES.bulb, trs(p.x, bridgeY(t) + 0.8, -p.y, 0.07, 0.08, 0.07), col("#FFE7A0"));
    }
    // stone arch faces under the deck
    for (const s of [1, -1]) for (let k = 0; k < 8; k++) {
      const t0 = 0.12 + (k / 8) * 0.76, t1 = 0.12 + ((k + 1) / 8) * 0.76;
      const p0 = add(add(mid, mul(n, (t0 - 0.5) * span)), mul(w, s * 1.01)), p1 = add(add(mid, mul(n, (t1 - 0.5) * span)), mul(w, s * 1.01));
      const arch = (t: number) => 0.03 + Math.sin(((t - 0.12) / 0.76) * Math.PI) * 0.2;
      m.quad(w3(p0, arch(t0)), w3(p1, arch(t1)), w3(p1, bridgeY(t1) - 0.1), w3(p0, bridgeY(t0) - 0.1), stone, [d.x * s, 0, -d.y * s]);
    }
    // short road stubs from each bridge end along the bank, where the street used to run
    for (const t of [0, 1]) {
      const e = add(mid, mul(n, (t - 0.5) * span));
      void e;
      for (const end of [a, b]) {
        // a paved lane along the sandy bank, from the street corner to the bridge
        const s = t ? 1 : -1;
        const p0 = add(end, mul(n, s * BANK_LANE)), p1 = add(mid, mul(n, s * BANK_LANE));
        const dd = norm(sub(p1, p0)), nn = v2(-dd.y * 0.2, dd.x * 0.2);
        m.quad(w3(add(p0, nn), 0.036), w3(add(p1, nn), 0.036), w3(sub(p1, nn), 0.036), w3(sub(p0, nn), 0.036), road, [0, 1, 0]);
      }
    }
  }
  const mat = ghost
    ? new THREE.MeshBasicMaterial({ vertexColors: true, transparent: true, opacity: 0.75, depthWrite: false })
    : new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.85 });
  const mesh = new THREE.Mesh(m.build(), mat);
  mesh.castShadow = !ghost;
  grp.add(mesh);
  return grp;
}

const mid2 = (a: V2, b: V2): V2 => v2((a.x + b.x) / 2, (a.y + b.y) / 2);
