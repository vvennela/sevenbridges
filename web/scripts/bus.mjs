// r21: buses and the river: bridge off (route blocked) and on (buses ride the deck).
import { chromium } from "playwright";
const out = "/tmp/sb-shots/r21-bus";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto("http://localhost:5173/?nocoach&test&mock", { timeout: 300000 });
await page.waitForSelector("#loading.gone", { timeout: 120000 });
await page.waitForTimeout(5000);
for (const r of [0, 1]) await page.locator(`[data-route='${r}']`).click().catch(() => {});
await page.mouse.move(700, 30);
await page.waitForTimeout(1500);
console.log("blocked (bridges off):", JSON.stringify(await page.evaluate(() => window.__sb.blocked())));
await page.screenshot({ path: `${out}-off.png` });
await page.evaluate(() => window.__sb.lookBridge(0, 5, 0.75));
await page.waitForTimeout(1500);
await page.screenshot({ path: `${out}-off-close.png` });
const sites = await page.evaluate(() => window.__sb.bridgeSites());
await page.click("[data-act='recenter']"); await page.waitForTimeout(800);
const s0 = (await page.evaluate(() => window.__sb.bridgeSites()))[0];
if (s0?.p) { await page.mouse.click(s0.p.x, s0.p.y); await page.waitForTimeout(800); }
await page.mouse.move(700, 30); await page.waitForTimeout(800);
await page.screenshot({ path: `/tmp/sb-shots/r21-bridge-default.png` });
await page.evaluate(() => window.__sb.setAllBridges(true)); await page.waitForTimeout(800);
await page.mouse.move(700, 30);
await page.waitForTimeout(1500);
console.log(JSON.stringify(await page.evaluate(() => window.__sb.dbgRiver())));
console.log("blocked (bridges on):", JSON.stringify(await page.evaluate(() => window.__sb.blocked())), "sites:", sites.length);
await page.screenshot({ path: `${out}-on.png` });
for (const [k, [d, e]] of [[4.5, 0.45], [3.6, 1.0]].entries()) {
  await page.evaluate(([d, e]) => window.__sb.lookBridge(0, d, e), [d, e]);
  if (k === 1) await page.mouse.move(1435, 450);
  for (let j = 1; j <= 3; j++) { await page.waitForTimeout(1300); await page.screenshot({ path: `/tmp/sb-shots/r21-bridge-angle${k + 1}-${j}.png` }); }
}
await browser.close();
