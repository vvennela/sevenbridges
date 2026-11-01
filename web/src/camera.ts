// Map camera: trackpad-first controls, like a maps app.
//  - two-finger scroll pans; pinch (wheel + ctrlKey) zooms; a mouse wheel zooms
//  - zoom goes toward the cursor; every change eases in over ~150 ms (no long drift)
//  - left-drag pans (a click only becomes a drag after 5 px, so clicks still build)
//  - right-drag or Option/Alt-drag orbits around the vertical axis; elevation is clamped
//  - the target stays near the town, and the camera never goes under the ground
import * as THREE from "three";

export interface CamState { target: THREE.Vector3; dist: number; az: number; polar: number }

export class MapCamera {
  cur: CamState;
  goal: CamState;
  minDist = 3;
  maxDist = 80;
  /** From nearly top-down to a low side view (the camera always stays above the ground). */
  minPolar = THREE.MathUtils.degToRad(6);
  maxPolar = THREE.MathUtils.degToRad(80);
  center = new THREE.Vector3();
  bound = 12;
  /** True while the pointer is dragging (the click handler should ignore this pointer-up). */
  dragged = false;
  private ray = new THREE.Raycaster();
  private plane = new THREE.Plane(new THREE.Vector3(0, 1, 0), 0);

  constructor(private camera: THREE.PerspectiveCamera, private el: HTMLElement) {
    const s = { target: new THREE.Vector3(), dist: 30, az: 0.5, polar: 0.9 };
    this.cur = { ...s, target: s.target.clone() };
    this.goal = { ...s, target: s.target.clone() };
    this.bind();
  }

  /** Jump to (or ease toward) a view. */
  set(target: THREE.Vector3, dist: number, az: number, polar: number, snap = false) {
    this.goal = { target: target.clone(), dist, az, polar };
    this.clamp(this.goal);
    if (snap) this.cur = { ...this.goal, target: this.goal.target.clone() };
  }

  /** Adopt whatever the camera currently shows (after code moved the camera directly). */
  syncFromCamera(target: THREE.Vector3, loose = false) {
    const off = this.camera.position.clone().sub(target);
    const dist = off.length();
    const polar = Math.acos(Math.max(-1, Math.min(1, off.y / dist)));
    const az = Math.atan2(off.x, off.z);
    this.cur = { target: target.clone(), dist, az, polar };
    this.goal = { target: target.clone(), dist, az, polar };
    if (!loose) this.clamp(this.goal);
  }

  /** Free the limits (debug screenshots use very low or close views). */
  loose = false;

  private clamp(s: CamState) {
    if (this.loose) return;
    s.dist = Math.max(this.minDist, Math.min(this.maxDist, s.dist));
    s.polar = Math.max(this.minPolar, Math.min(this.maxPolar, s.polar));
    // keep the town on screen: the target stays within a soft circle around the town
    const d = new THREE.Vector3(s.target.x - this.center.x, 0, s.target.z - this.center.z);
    if (d.length() > this.bound) d.setLength(this.bound);
    s.target.set(this.center.x + d.x, 0, this.center.z + d.z);
  }

  /** Ease toward the goal; call once per frame. */
  update(dt: number) {
    const k = 1 - Math.exp(-dt / 0.05);
    const c = this.cur, g = this.goal;
    c.target.lerp(g.target, k);
    c.dist += (g.dist - c.dist) * k;
    let dAz = g.az - c.az;
    dAz = Math.atan2(Math.sin(dAz), Math.cos(dAz));
    c.az += dAz * k;
    c.polar += (g.polar - c.polar) * k;
    const sp = Math.sin(c.polar);
    this.camera.position.set(c.target.x + c.dist * sp * Math.sin(c.az), c.target.y + c.dist * Math.cos(c.polar), c.target.z + c.dist * sp * Math.cos(c.az));
    this.camera.lookAt(c.target);
  }

  private groundAt(x: number, y: number): THREE.Vector3 | null {
    const r = this.el.getBoundingClientRect();
    const ndc = new THREE.Vector2(((x - r.left) / r.width) * 2 - 1, -((y - r.top) / r.height) * 2 + 1);
    this.ray.setFromCamera(ndc, this.camera);
    const hit = new THREE.Vector3();
    return this.ray.ray.intersectPlane(this.plane, hit) ? hit : null;
  }

  /** Zoom by a factor (<1 = closer), keeping the ground point under the cursor in place. */
  zoomAt(factor: number, x: number, y: number) {
    const g = this.goal;
    const before = g.dist;
    g.dist = Math.max(this.minDist, Math.min(this.maxDist, g.dist * factor));
    const p = this.groundAt(x, y);
    if (p) g.target.add(p.sub(g.target).multiplyScalar(1 - g.dist / before));
    this.clamp(g);
  }

  /** Pan by screen pixels (grab-style: content follows the fingers). */
  panPixels(dx: number, dy: number) {
    const g = this.goal;
    const perPx = (2 * g.dist * Math.tan(THREE.MathUtils.degToRad(this.camera.fov / 2))) / this.el.clientHeight;
    const right = new THREE.Vector3(Math.cos(g.az), 0, -Math.sin(g.az));
    const fwd = new THREE.Vector3(-Math.sin(g.az), 0, -Math.cos(g.az));
    // vertical screen motion maps to ground distance stretched by the view angle
    const stretch = 1 / Math.max(0.35, Math.cos(g.polar));
    g.target.addScaledVector(right, -dx * perPx).addScaledVector(fwd, dy * perPx * Math.min(stretch, 2.2));
    this.clamp(g);
  }

  /** Turn around the vertical axis and tilt (radians), eased like every other move. */
  turnTilt(dAz: number, dPolar: number) {
    this.loose = false;
    this.goal.az += dAz;
    this.goal.polar += dPolar;
    this.clamp(this.goal);
  }

  orbit(dx: number, dy: number) {
    this.goal.az -= dx * 0.006;
    this.goal.polar -= dy * 0.004;
    this.clamp(this.goal);
  }

  private bind() {
    const el = this.el;
    el.addEventListener("wheel", (e) => {
      e.preventDefault();
      this.loose = false;
      if (e.ctrlKey) {
        // pinch on a trackpad (the browser sends wheel + ctrlKey)
        this.zoomAt(Math.exp(Math.max(-0.25, Math.min(0.25, e.deltaY * 0.01))), e.clientX, e.clientY);
      } else if (e.deltaMode === 1 || (e.deltaX === 0 && Math.abs(e.deltaY) >= 40 && Number.isInteger(e.deltaY))) {
        // a mouse wheel: one gentle step per notch
        this.zoomAt(Math.exp(Math.sign(e.deltaY) * 0.14), e.clientX, e.clientY);
      } else {
        // two-finger scroll on a trackpad: pan (momentum deltas are capped per event)
        const cap = (v: number) => Math.max(-60, Math.min(60, v));
        this.panPixels(-cap(e.deltaX), -cap(e.deltaY));
      }
    }, { passive: false });

    // Safari trackpads: two-finger rotate turns the town
    let gRot = 0;
    el.addEventListener("gesturestart", (e) => { e.preventDefault(); gRot = (e as unknown as { rotation: number }).rotation ?? 0; });
    el.addEventListener("gesturechange", (e) => {
      e.preventDefault();
      const r = (e as unknown as { rotation: number }).rotation ?? 0;
      this.turnTilt(-THREE.MathUtils.degToRad(r - gRot), 0);
      gRot = r;
    });
    let down: { x: number; y: number; button: number; alt: boolean } | null = null;
    let last = { x: 0, y: 0 };
    let mode: "none" | "pan" | "orbit" = "none";
    el.addEventListener("pointerdown", (e) => {
      down = { x: e.clientX, y: e.clientY, button: e.button, alt: e.altKey };
      last = { x: e.clientX, y: e.clientY };
      mode = "none";
      this.dragged = false;
    });
    window.addEventListener("pointermove", (e) => {
      if (!down) return;
      if (mode === "none" && Math.hypot(e.clientX - down.x, e.clientY - down.y) > 5) {
        mode = down.button === 2 || down.alt ? "orbit" : down.button === 0 ? "pan" : "none";
        if (mode !== "none") { this.dragged = true; this.loose = false; el.setPointerCapture?.(e.pointerId); }
      }
      const dx = e.clientX - last.x, dy = e.clientY - last.y;
      last = { x: e.clientX, y: e.clientY };
      if (mode === "pan") this.panPixels(dx, dy);
      else if (mode === "orbit") this.orbit(dx, dy);
    });
    const end = () => { down = null; mode = "none"; };
    window.addEventListener("pointerup", end);
    window.addEventListener("pointercancel", end);
    window.addEventListener("blur", end);
  }
}
