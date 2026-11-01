// Soft overlays on the map: air (haze over polluted blocks, fresh air over parks),
// busy streets, and the "who affects whom" links shown when hovering a block.
// Looks only: how much haze, which streets are busy and which links exist all come
// from Lean's report; this file only draws them.
import * as THREE from "three";
import { GB, col, w3 } from "./builder";
import { add, mul, norm, sub, v2, type V2 } from "./geom";

function softTexture(inner: string, outer: string): THREE.CanvasTexture {
  const cv = document.createElement("canvas");
  cv.width = cv.height = 128;
  const g = cv.getContext("2d")!;
  const gr = g.createRadialGradient(64, 64, 4, 64, 64, 62);
  gr.addColorStop(0, inner);
  gr.addColorStop(1, outer);
  g.fillStyle = gr;
  g.fillRect(0, 0, 128, 128);
  const t = new THREE.CanvasTexture(cv);
  t.colorSpace = THREE.SRGBColorSpace;
  return t;
}

/** A lumpy smog cloud: overlapping soft blobs, darker at the bottom. */
const HAZE_TEX = (() => {
  const cv = document.createElement("canvas");
  cv.width = 256; cv.height = 128;
  const g = cv.getContext("2d")!;
  const blob = (x: number, y: number, r: number, a: number) => {
    const gr = g.createRadialGradient(x, y, r * 0.2, x, y, r);
    gr.addColorStop(0, `rgba(255,255,255,${a})`);
    gr.addColorStop(1, "rgba(255,255,255,0)");
    g.fillStyle = gr;
    g.beginPath(); g.arc(x, y, r, 0, Math.PI * 2); g.fill();
  };
  for (const [x, y, r] of [[70, 74, 46], [118, 58, 54], [170, 70, 48], [128, 86, 50], [96, 92, 36], [190, 92, 30]]) blob(x, y, r, 0.9);
  const t = new THREE.CanvasTexture(cv);
  t.colorSpace = THREE.SRGBColorSpace;
  return t;
})();
void softTexture;
const SPARK_TEX = (() => {
  const cv = document.createElement("canvas");
  cv.width = cv.height = 64;
  const g = cv.getContext("2d")!;
  g.fillStyle = "#ffffff";
  g.beginPath();
  for (let k = 0; k < 8; k++) { const a = (k / 8) * Math.PI * 2, r = k % 2 ? 9 : 28; g.lineTo(32 + Math.cos(a) * r, 32 + Math.sin(a) * r); }
  g.fill();
  const t = new THREE.CanvasTexture(cv);
  t.colorSpace = THREE.SRGBColorSpace;
  return t;
})();

interface Puff { s: THREE.Sprite; c: V2; r: number; ph: number; h: number; size: number; op: number; spark: boolean }

export class Air {
  readonly group = new THREE.Group();
  private puffs: Puff[] = [];
  constructor(parent: THREE.Object3D) { parent.add(this.group); }

  /**
   * `level[i]`: 0..1, how polluted block i is (Lean's pollution, divided by the town's highest).
   * `fresh`: blocks with clean air to show (parks, when Lean reports pollution).
   */
  set(centers: V2[], level: (number | null)[], fresh: number[], radiusOf: (i: number) => number) {
    for (const p of this.puffs) { this.group.remove(p.s); p.s.material.dispose(); }
    this.puffs = [];
    level.forEach((lv, i) => {
      if (!lv || lv <= 0.02) return;
      const n = 2 + Math.round(lv * 4);
      const R = radiusOf(i);
      for (let k = 0; k < n; k++) {
        const mat = new THREE.SpriteMaterial({ map: HAZE_TEX, color: col(lv > 0.6 ? "#9E9282" : lv > 0.3 ? "#ADA393" : "#BDB6AA"), transparent: true, opacity: 0, depthWrite: false });
        const s = new THREE.Sprite(mat);
        s.renderOrder = 6;
        this.group.add(s);
        const a = (k / n) * Math.PI * 2 + i * 1.3;
        const rr = R * (k === 0 ? 0 : 0.45);
        this.puffs.push({ s, c: add(centers[i], v2(Math.cos(a) * rr, Math.sin(a) * rr)), r: 0.3, ph: k * 1.7 + i, h: 2.2 + (k % 3) * 0.35, size: Math.min(3.0, R * 0.7) * (0.8 + lv * 0.3), op: 0.18 + lv * 0.24, spark: false });
      }
    });
    for (const i of fresh) {
      const R = radiusOf(i);
      for (let k = 0; k < 9; k++) {
        const mat = new THREE.SpriteMaterial({ map: SPARK_TEX, color: col(k % 2 ? "#FFFFFF" : "#C8F5DF"), transparent: true, opacity: 0, depthWrite: false });
        const s = new THREE.Sprite(mat);
        s.renderOrder = 6;
        this.group.add(s);
        const a = k * 2.4;
        this.puffs.push({ s, c: add(centers[i], v2(Math.cos(a) * R * 0.5 * ((k % 3) / 3 + 0.3), Math.sin(a) * R * 0.5 * ((k % 3) / 3 + 0.3))), r: 0.1, ph: k * 0.73 + i, h: 0.5, size: 0.16, op: 0.9, spark: true });
      }
    }
  }

  update(t: number, cam?: THREE.Vector3) {
    for (const p of this.puffs) {
      if (p.spark) {
        // fresh air: little twinkles rising slowly over the park, fading in and out
        const u = ((t * 0.18 + p.ph) % 1 + 1) % 1;
        p.s.position.set(p.c.x + Math.sin(t * 0.6 + p.ph) * 0.15, 0.4 + u * 1.6, -p.c.y);
        const sz = p.size * 1.6 * (0.6 + 0.4 * Math.sin(t * 3 + p.ph * 5));
        p.s.scale.set(sz, sz, 1);
        p.s.material.opacity = p.op * Math.sin(u * Math.PI);
        continue;
      }
      // haze: big soft blobs drifting slowly in place
      const a = t * 0.12 + p.ph;
      p.s.position.set(p.c.x + Math.cos(a) * p.r, p.h + Math.sin(t * 0.3 + p.ph) * 0.15, -(p.c.y + Math.sin(a) * p.r));
      const sz = p.size * (1 + 0.08 * Math.sin(t * 0.4 + p.ph));
      p.s.scale.set(sz * 2, sz, 1);
      // fade out when the camera comes close, so the haze never fills the screen
      const near = cam ? Math.min(1, Math.max(0, (cam.distanceTo(p.s.position) - 4) / 6)) : 1;
      p.s.material.opacity = p.op * near * (0.85 + 0.15 * Math.sin(t * 0.5 + p.ph));
    }
  }
}

/** Busy streets: a warm translucent wash over each segment, stronger with more traffic. */
export function trafficWash(segs: [V2, V2][], level: number[], width: number, opacity = 0.55, yAt = 0.022): THREE.Mesh | null {
  const m = new GB();
  segs.forEach(([a, b], i) => {
    const lv = level[i] ?? 0;
    if (lv <= 0.05) return;
    const d = norm(sub(b, a)), n = v2(-d.y * width / 2, d.x * width / 2);
    const c = col(lv > 0.66 ? "#F28B6E" : lv > 0.33 ? "#F7B27A" : "#F9D79A");
    const y = yAt; // by default above the road, below the river's banks and water
    m.quad(w3(add(a, n), y), w3(add(b, n), y), w3(sub(b, n), y), w3(sub(a, n), y), c, [0, 1, 0]);
  });
  if (m.empty) return null;
  const mesh = new THREE.Mesh(m.build(), new THREE.MeshBasicMaterial({ vertexColors: true, transparent: true, opacity, depthWrite: false }));
  mesh.renderOrder = yAt > 0.03 ? 4 : 2;
  return mesh;
}

export interface Link { from: V2; to: V2; tone: "good" | "bad" | "mixed" | "work" | "none" }
const TONE = { good: "#5FBF6A", bad: "#E2675A", mixed: "#F5A93E", work: "#4F7FD0", none: "#B9B4CC" };

/** Soft arcs between blocks (hovered block → its neighbors), drawn over everything. */
export function linkArcs(links: Link[]): THREE.Group {
  const g = new THREE.Group();
  for (const l of links) {
    const pts: THREE.Vector3[] = [];
    const lift = 0.9 + Math.hypot(l.to.x - l.from.x, l.to.y - l.from.y) * 0.08;
    for (let k = 0; k <= 24; k++) {
      const t = k / 24;
      const p = add(l.from, mul(sub(l.to, l.from), t));
      pts.push(new THREE.Vector3(p.x, 0.5 + Math.sin(t * Math.PI) * lift, -p.y));
    }
    const curve = new THREE.CatmullRomCurve3(pts);
    const tube = new THREE.Mesh(new THREE.TubeGeometry(curve, 32, l.tone === "none" ? 0.035 : 0.055, 6, false), new THREE.MeshBasicMaterial({ color: col(TONE[l.tone]), transparent: true, opacity: l.tone === "none" ? 0.6 : 0.85, depthTest: false }));
    tube.renderOrder = 14;
    g.add(tube);
    // a dot at the far end
    const end = new THREE.Mesh(new THREE.SphereGeometry(0.12, 12, 8), tube.material);
    end.position.copy(pts[pts.length - 1]);
    end.renderOrder = 14;
    g.add(end);
  }
  return g;
}

/** The top of an arc (for placing its label). */
export function arcTop(a: V2, b: V2, t = 0.5): { p: V2; h: number } {
  const lift = 0.9 + Math.hypot(b.x - a.x, b.y - a.y) * 0.08;
  return { p: add(a, mul(sub(b, a), t)), h: 0.5 + Math.sin(t * Math.PI) * lift };
}
