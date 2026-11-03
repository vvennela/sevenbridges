// Play the tutorial the way a new player does: Start on a fresh device opens the
// tutorial town; do what each bubble asks; check it ends and is not shown again.
// Usage: node scripts/tutorial-e2e.mjs [url] [shots-dir] [width] [height]
import { chromium } from "playwright";

const url = process.argv[2] ?? "http://localhost:5173/";
const shots = process.argv[3] ?? null;
const W = Number(process.argv[4] ?? 1440), H = Number(process.argv[5] ?? 900);
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: W, height: H } });
const errors = [];
page.on("pageerror", (e) => errors.push(e.message));
const fail = (m) => { console.log("FAIL:", m); process.exitCode = 1; };
const snap = async (n) => { if (shots) await page.screenshot({ path: `${shots}/${W}x${H}-${n}.png` }); };
const title = async () => (await page.textContent("#tut h3").catch(() => ""))?.trim();
const step = async (want) => {
  await page.waitForFunction((t) => document.querySelector("#tut:not(.hidden) h3")?.textContent === t, want, { timeout: 15000 }).catch(() => {});
  const t = await title();
  if (t !== want) fail(`expected step "${want}", saw "${t}"`); else console.log("step:", t);
  // the bubble is on screen
  const r = await page.$eval("#tut", (e) => { const b = e.getBoundingClientRect(); return { l: b.left, t: b.top, r: b.right, b: b.bottom }; });
  if (r.l < 0 || r.t < 0 || r.r > W || r.b > H) fail(`bubble off screen at "${want}": ${JSON.stringify(r)}`);
  await page.waitForTimeout(400);
  await snap(want.replace(/\W+/g, "-").toLowerCase());
};
// a block on screen: try points around the middle until a click builds something
async function clickBlock() {
  const before = await page.$eval("#meter .bar-val", (e) => e.textContent);
  for (const [fx, fy] of [[0.5, 0.5], [0.45, 0.45], [0.55, 0.55], [0.4, 0.55], [0.6, 0.45], [0.5, 0.38], [0.5, 0.62], [0.35, 0.5], [0.65, 0.5]]) {
    await page.mouse.click(W * fx, H * fy);
    await page.waitForTimeout(500);
    if ((await page.$eval("#meter .bar-val", (e) => e.textContent)) !== before) return true;
  }
  return false;
}

await page.goto(url);
await page.waitForSelector(".title-card.on [data-act='start']", { timeout: 60000 });
await page.click(".title-card.on [data-act='start']");
await page.waitForSelector(".intro-card", { timeout: 120000 });
const kicker = (await page.textContent(".intro-kicker"))?.trim();
if (kicker !== "Your first town") fail(`Start did not open the tutorial (kicker "${kicker}")`);
await snap("0-intro");
await page.click("[data-act='go']");

await step("Meet your residents");
await page.click("[data-tut='next']");
await step("Pick a building");
await page.click("[data-tool='housing']");
await step("Build on a block");
if (!(await clickBlock())) fail("no block took a building");
await step("Fill your town");
await page.click("[data-tut='next']");
await step("Look through a lens");
await page.click("[data-lens='mood']");
await step("Connect the town");
await page.click("[data-route='0']");
await step("Build it");
await page.click("#build");
await step("Your rating");
await page.click("[data-tut='next']");
await page.waitForTimeout(300);
if (!(await page.$eval("#tut", (e) => e.classList.contains("hidden")))) fail("tutorial did not close");
if ((await page.evaluate(() => localStorage.getItem("sb-tutorial-done"))) !== "1") fail("tutorial not remembered");

// a second visit goes straight to the size picker
await page.goto(url);
await page.waitForSelector(".title-card.on [data-act='start']", { timeout: 60000 });
await page.click(".title-card.on [data-act='start']");
if (!(await page.isVisible("[data-pick='easy']"))) fail("second Start did not show the size picker");
// and the rules screen can replay it
await page.click(".title-card.on [data-act='home']");
await page.click(".title-card.on [data-act='rules']");
await page.click(".title-card.on [data-act='tutorial']");
await page.waitForSelector(".intro-card", { timeout: 120000 });
await page.click("[data-act='go']");
await step("Meet your residents");
await page.click("[data-tut='skip']");
if (!(await page.$eval("#tut", (e) => e.classList.contains("hidden")))) fail("Skip did not close the tutorial");

if (errors.length) fail(`page errors: ${errors.join(" | ")}`);
console.log(process.exitCode ? "tutorial: FAILED" : "tutorial: all steps OK");
await browser.close();
