// Living background: wide view, river with traffic, motion sequence, dusk, build-tool dimming, fps.
// Usage: node scripts/bg.mjs [outPrefix] [seed] [size]
import { chromium } from "playwright";
const out = process.argv[2] ?? "/tmp/sb-shots/bg";
const seed = process.argv[3] ?? "4242", size = process.argv[4] ?? "medium", extra = process.argv[5] ? "&" + process.argv[5] : "";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
page.on("console", (m) => { if (m.type() === "error") console.log("[console]", m.text()); });
const shot = async (n) => { await page.screenshot({ path: `${out}-${n}.png` }); console.log("shot", n); };
await page.goto(`http://localhost:5173/?seed=${seed}&size=${size}&test&nocoach&nointro${extra}`);
await page.waitForSelector("#tools .tile", { timeout: 90000 });
await page.waitForTimeout(1000);
const bs = await page.evaluate(() => window.__sb.blocks());
const plan = ["housing", "office", "food", "housing", "park", "shop", "bar", "housing"];
for (const [i, b] of bs.entries()) {
  await page.locator(`[data-tool='${plan[i % plan.length]}']`).click({ timeout: 1500 }).catch(() => {});
  await page.mouse.click(b.p.x, b.p.y + 20);
  await page.waitForTimeout(100);
}
await page.keyboard.press("Escape");
await page.evaluate(() => window.__sb.setAllBridges(true));
await page.waitForTimeout(300);
await page.locator("[data-route='0']").click().catch(() => {});
await page.mouse.move(1435, 600);
await page.waitForTimeout(3500);
await shot("play");
const fps = await page.evaluate(() => new Promise((res) => { let n = 0; const t0 = performance.now(); const f = () => { n++; if (performance.now() - t0 < 3000) requestAnimationFrame(f); else res(Math.round(n / 3)); }; requestAnimationFrame(f); }));
console.log("fps:", fps, "renderer:", JSON.stringify(await page.evaluate(() => window.__sb.info())));
await page.evaluate(() => window.__sb.zoom(1.9));
await page.waitForTimeout(1500);
await shot("wide");
await page.evaluate(() => window.__sb.far());
await page.waitForTimeout(1500);
await shot("wide-low");
await page.evaluate(() => window.__sb.recenter());
await page.waitForTimeout(800);
// river close-ups with traffic
const sites = await page.evaluate(() => window.__sb.bridgeSites());
if (sites.length) {
  await page.evaluate(() => window.__sb.lookBridge(0, 11, 0.7));
  for (const k of [1, 2, 3]) { await page.waitForTimeout(1300); await shot(`river-${k}`); }
}
// motion sequence on a home block (wind, clouds, cats)
await page.evaluate(() => window.__sb.lookBlock(0, 12, 0.6));
for (const k of [1, 2, 3]) { await page.waitForTimeout(1200); await shot(`motion-${k}`); }
await page.evaluate(() => window.__sb.recenter());
await page.locator("[data-tool='housing']").click();
await page.waitForTimeout(1200);
await shot("tool-dim");
await browser.close();
