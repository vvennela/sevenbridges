// Air lens and turn/tilt checks. Usage: node scripts/air.mjs [outDir-prefix-air] [outDir-prefix-rot]
import { chromium } from "playwright";
const A = process.argv[2] ?? "/tmp/sb-shots/air", R = process.argv[3] ?? "/tmp/sb-shots/rot";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto("http://localhost:5173/?seed=4242&size=medium&test&nocoach&nointro");
await page.waitForSelector("#tools .tile", { timeout: 90000 });
await page.waitForTimeout(800);
const bs = await page.evaluate(() => window.__sb.blocks());
const plan = ["housing", "office", "food", "housing", "park", "shop", "housing", "housing"];
for (const [i, b] of bs.entries()) {
  await page.locator(`[data-tool='${plan[i % plan.length]}']`).click({ timeout: 1500 }).catch(() => {});
  await page.mouse.click(b.p.x, b.p.y + 20);
  if (plan[i % plan.length] === "office") await page.mouse.click(b.p.x, b.p.y + 20);
  await page.waitForTimeout(100);
}
await page.keyboard.press("Escape");
await page.evaluate(() => window.__sb.setAllBridges(true));
await page.locator("[data-route='0']").click().catch(() => {});
await page.waitForTimeout(1500);
await page.click("[data-lens='air']");
await page.mouse.move(1435, 880);
await page.waitForTimeout(1500);
await page.screenshot({ path: `${A}-lens.png` });
const now = await page.evaluate(() => window.__sb.blocks());
for (const k of ["office", "park", "housing"]) {
  const b = now.find((x) => x.kind === k);
  if (!b) continue;
  await page.mouse.move(b.p.x, b.p.y + 20);
  await page.waitForTimeout(800);
  await page.screenshot({ path: `${A}-hover-${k}.png` });
  console.log(k, (await page.textContent("#card"))?.replace(/\s+/g, " ").trim());
}
await page.click("[data-lens='none']");
await page.mouse.move(1435, 880);
// turn and tilt: keyboard, then the pad
for (let k = 0; k < 4; k++) { await page.keyboard.press("e"); await page.waitForTimeout(60); }
await page.waitForTimeout(900);
await page.screenshot({ path: `${R}-turned.png` });
console.log("cam", JSON.stringify(await page.evaluate(() => window.__sb.cam())));
for (let k = 0; k < 6; k++) { await page.keyboard.press("r"); await page.waitForTimeout(60); }
await page.waitForTimeout(900);
await page.screenshot({ path: `${R}-topdown.png` });
console.log("cam", JSON.stringify(await page.evaluate(() => window.__sb.cam())));
const down = page.locator("[data-view='down']");
await down.hover(); await page.mouse.down(); await page.waitForTimeout(2200); await page.mouse.up();
await page.waitForTimeout(900);
await page.screenshot({ path: `${R}-low.png` });
console.log("cam", JSON.stringify(await page.evaluate(() => window.__sb.cam())));
await page.locator("[data-view='left']").hover();
await page.waitForTimeout(700);
await page.screenshot({ path: `${R}-tip.png`, clip: { x: 1000, y: 250, width: 440, height: 220 } });
await browser.close();
