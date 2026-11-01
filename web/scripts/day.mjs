// Lean's simulated day (mocked with ?mock until Lean sends report.cats): build, turn a bus on,
// and shoot the town at a few moments of the day.
import { chromium } from "playwright";
const out = process.argv[2] ?? "/tmp/sb-shots/v2-day";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto(`http://localhost:5173/?seed=4242&size=medium&mock&test&nocoach&nointro`);
await page.waitForSelector("#tools .tile", { timeout: 90000 });
await page.waitForTimeout(800);
const bs = await page.evaluate(() => window.__sb.blocks());
const plan = ["housing", "office", "food", "housing", "shop", "bar", "office"];
for (const [i, b] of bs.entries()) {
  await page.locator(`[data-tool='${plan[i % plan.length]}']`).click({ timeout: 2000 }).catch(() => {});
  await page.mouse.click(b.p.x, b.p.y + 20);
  await page.waitForTimeout(120);
}
await page.keyboard.press("Escape");
await page.locator("[data-route='0']").click();
await page.locator("[data-route='1']").click();
await page.mouse.move(1435, 600);
for (const k of [1, 2, 3, 4]) {
  await page.waitForTimeout(k === 1 ? 6000 : 14000);
  console.log("clock", JSON.stringify(await page.evaluate(() => window.__sb.day())));
  await page.screenshot({ path: `${out}-${k}.png` });
}
await browser.close();
