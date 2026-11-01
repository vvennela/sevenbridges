// Small 3D renders of the real building models, for the tray tiles.
import * as THREE from "three";
import { thumbModel } from "./buildings";

/** Render each kind once to a transparent PNG data URL. */
export function renderThumbs(kinds: string[], size = 160): Record<string, string> {
  const r = new THREE.WebGLRenderer({ antialias: true, alpha: true, preserveDrawingBuffer: true });
  r.setSize(size, size);
  r.setPixelRatio(1);
  r.outputColorSpace = THREE.SRGBColorSpace;
  r.toneMapping = THREE.ACESFilmicToneMapping;
  r.toneMappingExposure = 1.15;
  const scene = new THREE.Scene();
  scene.add(new THREE.HemisphereLight(0xd6ecff, 0xbfe0a0, 1.4));
  const sun = new THREE.DirectionalLight(0xffe4bd, 2.6);
  sun.position.set(-3, 6, 4);
  scene.add(sun);
  const cam = new THREE.PerspectiveCamera(26, 1, 0.1, 100);
  const out: Record<string, string> = {};
  for (const k of kinds) {
    const m = thumbModel(k);
    scene.add(m);
    const box = new THREE.Box3().setFromObject(m);
    const c = box.getCenter(new THREE.Vector3());
    const rad = box.getBoundingSphere(new THREE.Sphere()).radius;
    const d = rad / Math.sin(THREE.MathUtils.degToRad(13)) * 0.74;
    cam.position.set(c.x + d * 0.55, c.y + d * 0.62, c.z + d * 0.56);
    cam.lookAt(c);
    r.render(scene, cam);
    out[k] = r.domElement.toDataURL("image/png");
    scene.remove(m);
    m.traverse((o) => { if (o instanceof THREE.Mesh) o.geometry.dispose(); });
  }
  r.dispose();
  r.forceContextLoss();
  return out;
}
