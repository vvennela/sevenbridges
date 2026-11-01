// Tile diversity: fill every block of one town with each kind in turn and shoot the overview.
// Usage: node scripts/kinds.mjs [outPrefix] [seed] [size]
import { chromium } from "playwright";
const out = process.argv[2] ?? "/tmp/sb-shots/v2-kinds";
const seed = process.argv[3] ?? "4242", size = process.argv[4] ?? "hard";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto(`http://localhost:5173/?seed=${seed}&size=${size}&mock&test&nocoach&nointro`);
await page.waitForSelector("#tools .tile", { timeout: 90000 });
await page.waitForTimeout(1000);
for (const [k, n] of [["housing", 2], ["office", 3], ["shop", 1], ["park", 1], ["food", 1], ["bar", 1]]) {
  await page.evaluate(([k, n]) => window.__sb.setAll(k, n), [k, n]);
  await page.mouse.move(1435, 450);
  await page.waitForTimeout(2200);
  await page.screenshot({ path: `${out}-${k}.png` });
  console.log("shot", k);
}
await browser.close();
