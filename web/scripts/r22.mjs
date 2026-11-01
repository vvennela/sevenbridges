// r22: site markers only with the Subway tool, ghost bridges + Bridge tool, a bus and a cat on a bridge, difficulty.
import { chromium } from "playwright";
const out = "/tmp/sb-shots/r22";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto("http://localhost:5173/?nocoach&test", { timeout: 300000 });
await page.waitForSelector("#loading.gone", { timeout: 300000 });
await page.waitForTimeout(5000);
await page.mouse.move(700, 30);
await page.screenshot({ path: `${out}-plain.png` });
await page.locator("[data-tool='subway']").click(); await page.waitForTimeout(800);
await page.screenshot({ path: `${out}-subway-tool.png` });
await page.locator("[data-tool='bridge']").click(); await page.waitForTimeout(800);
await page.screenshot({ path: `${out}-bridge-tool.png` });
await page.keyboard.press("Escape");
const n = (await page.evaluate(() => window.__sb.bridgeSites())).length;
console.log("bridge sites:", n);
await page.evaluate(() => window.__sb.setAllBridges(true));
for (const r of [0, 1, 2]) await page.locator(`[data-route='${r}']`).click().catch(() => {});
await page.mouse.move(700, 30);
await page.waitForTimeout(1500);
console.log("blocked:", JSON.stringify(await page.evaluate(() => window.__sb.blocked())), JSON.stringify(await page.evaluate(() => window.__sb.dbgRiver())));
await page.screenshot({ path: `${out}-built.png` });
await page.evaluate(() => window.__sb.lookBridge(0, 7.5, 0.62));
await page.mouse.move(1435, 450);
let got = false;
for (let k = 0; k < 120 && !got; k++) { if (await page.evaluate(() => window.__sb.busOnBridge())) { got = true; await page.screenshot({ path: `${out}-bus-on-bridge.png` }); } else await page.waitForTimeout(250); }
console.log("bus on bridge captured:", got);
await page.evaluate(() => window.__sb.bridgeWalk(0));
await page.evaluate(() => window.__sb.lookBridge(0, 5, 0.5));
for (let k = 1; k <= 3; k++) { await page.waitForTimeout(1300); await page.screenshot({ path: `${out}-cat-on-bridge-${k}.png` }); }
await page.goto("http://localhost:5173/?nocoach&test&seed=777&size=easy", { timeout: 300000 });
await page.waitForSelector("#loading.gone", { timeout: 300000 });
await page.waitForTimeout(4000);
await page.screenshot({ path: `${out}-easy.png` });
console.log("title:", (await page.textContent(".town-head"))?.replace(/\s+/g, " "), "|", await page.textContent(".diff"));
await browser.close();
