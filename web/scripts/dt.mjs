// Downtown checks: title, default view, low tilt facing downtown, dusk.
import { chromium } from "playwright";
const out = process.argv[2] ?? "/tmp/sb-shots/dt";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
const shot = async (n) => { await page.screenshot({ path: `${out}-${n}.png` }); console.log("shot", n); };
await page.goto("http://localhost:5173/?test");
await page.waitForSelector(".title-card.on", { timeout: 60000 });
await page.waitForTimeout(2500);
await shot("title");
for (const tod of ["", "&tod=3.45"]) {
  await page.goto(`http://localhost:5173/?seed=4242&size=medium&test&nocoach&nointro${tod}`);
  await page.waitForSelector("#tools .tile", { timeout: 90000 });
  await page.waitForTimeout(2500);
  const tag = tod ? "dusk-" : "";
  if (!tod) await shot("default");
  // low tilt, looking toward downtown (the default view already faces it)
  for (let k = 0; k < 10; k++) { await page.keyboard.press("f"); await page.waitForTimeout(50); }
  await page.waitForTimeout(1500);
  await shot(`${tag}low`);
  await page.evaluate(() => window.__sb.zoom(0.55));
  await page.waitForTimeout(1500);
  await shot(`${tag}low-close`);
}
console.log("renderer:", JSON.stringify(await page.evaluate(() => window.__sb.info())));
await browser.close();
