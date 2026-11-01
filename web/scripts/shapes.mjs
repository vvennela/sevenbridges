// Six new towns through the real Start flow, one screenshot each (whole town in view).
// Usage: node scripts/shapes.mjs [outPrefix] [count]
import { chromium } from "playwright";
import { designFor } from "../../tools/genmap.mjs";
const out = process.argv[2] ?? "/tmp/sb-shots/shape", count = Number(process.argv[3] ?? 6);
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
const sizes = ["easy", "medium", "hard"];
for (let k = Number(process.argv[4] ?? 0); k < count; k++) {
  await page.goto("http://localhost:5173/?test&nocoach");
  await page.waitForSelector(".title-card.on", { timeout: 60000 });
  await page.click(".title-card.on [data-act='start']");
  await page.click(`[data-pick='${sizes[k % 3]}']`);
  await page.waitForSelector(".intro-card", { timeout: 400000 });
  const name = (await page.textContent(".intro-card h2"))?.trim();
  const seed = Number(name?.replace(/\D/g, ""));
  await page.click("[data-act='go']");
  await page.mouse.move(1435, 600);
  await page.evaluate(() => window.__sb.zoom(1.35));
  await page.waitForTimeout(2500);
  const d = designFor(seed);
  console.log(k + 1, name, sizes[k % 3], `${d.family}/${d.river}`);
  await page.screenshot({ path: `${out}-${k + 1}.png` });
}
await browser.close();
