// Responsive pass: screenshots of every screen at many sizes, combined into one contact sheet per size.
// Usage: node scripts/resp.mjs [WxH@dpr ...]
import { chromium } from "playwright";
import { writeFileSync } from "node:fs";
const sizes = process.argv.length > 2 ? process.argv.slice(2) : ["1920x1080@1", "1680x1050@1", "1440x900@1", "1366x768@1", "1280x800@1", "1280x720@1", "1024x768@1", "390x844@2", "844x390@2", "1440x900@2"];
const browser = await chromium.launch({ args: ["--use-angle=metal", "--autoplay-policy=no-user-gesture-required"] });
const report = [];
for (const spec of sizes) {
  const [wh, dpr] = spec.split("@"); const [W, H] = wh.split("x").map(Number);
  const page = await browser.newPage({ viewport: { width: W, height: H }, deviceScaleFactor: Number(dpr) });
  const errs = []; page.on("pageerror", (e) => errs.push(e.message));
  const shots = [];
  const tag = `${W}x${H}@${dpr}`;
  const shot = async (n) => { const f = `/tmp/sb-shots/resp-${tag}-${n}.png`; await page.screenshot({ path: f }); shots.push([n, f]); };
  /** Layout problems: HUD boxes overlapping each other or off-screen, text clipped. */
  const audit = async (n) => {
    const r = await page.evaluate(() => {
      const vis = (e) => { const s = getComputedStyle(e); const b = e.getBoundingClientRect(); return s.display !== "none" && s.visibility !== "hidden" && b.width > 0 && b.height > 0 && !e.closest(".hidden"); };
      const ids = ["town", "meter", "lenses", "viewpad", "legend", "tray", "music", "postcard", "card", "dayclock", "coach", "intro", "confirm"];
      const boxes = ids.map((id) => document.getElementById(id)).filter((e) => e && vis(e)).map((e) => ({ id: e.id, r: e.getBoundingClientRect() }));
      const out = [];
      for (const b of boxes) {
        if (b.r.left < -1 || b.r.top < -1 || b.r.right > innerWidth + 1 || b.r.bottom > innerHeight + 1) out.push(`${b.id} off-screen (${Math.round(b.r.left)},${Math.round(b.r.top)},${Math.round(b.r.right)},${Math.round(b.r.bottom)})`);
      }
      const skip = new Set(["intro", "confirm"]);
      for (let i = 0; i < boxes.length; i++) for (let j = i + 1; j < boxes.length; j++) {
        const a = boxes[i], c = boxes[j];
        if (skip.has(a.id) || skip.has(c.id)) continue;
        const ov = Math.min(a.r.right, c.r.right) - Math.max(a.r.left, c.r.left), oh = Math.min(a.r.bottom, c.r.bottom) - Math.max(a.r.top, c.r.top);
        if (ov > 2 && oh > 2) out.push(`${a.id} overlaps ${c.id} (${Math.round(ov)}x${Math.round(oh)})`);
      }
      // clipped text inside fixed boxes (ellipsis is fine)
      for (const e of document.querySelectorAll("#hud button, #hud .card-title, #hud h1, #hud h2, .tile-name, .pair-cell span")) {
        if (!vis(e)) continue;
        const s = getComputedStyle(e);
        if (s.textOverflow !== "ellipsis" && e.scrollWidth > e.clientWidth + 2 && s.overflow !== "visible") out.push(`clipped: "${e.textContent.trim().slice(0, 24)}"`);
      }
      // canvas matches the window
      const cv = document.querySelector("#scene canvas");
      if (cv && (Math.abs(cv.clientWidth - innerWidth) > 1 || Math.abs(cv.clientHeight - innerHeight) > 1 || Math.abs(cv.width - innerWidth * Math.min(devicePixelRatio, 2)) > 2)) out.push(`canvas ${cv.width}x${cv.height} (css ${cv.clientWidth}x${cv.clientHeight}) for ${innerWidth}x${innerHeight}@${devicePixelRatio}`);
      return out;
    });
    for (const x of r) report.push(`${tag} ${n}: ${x}`);
  };
  try {
  await page.goto("http://localhost:5173/?test");
  await page.waitForSelector(".title-card.on", { timeout: 60000 });
  await page.waitForTimeout(1500);
  await shot("1-title"); await audit("title");
  await page.click("[data-act='rules']"); await page.waitForTimeout(500); await shot("2-rules"); await audit("rules");
  await page.click(".title-card.on [data-act='start']"); await page.waitForTimeout(500); await shot("3-size"); await audit("size");
  await page.goto(`http://localhost:5173/?seed=4242&size=medium&test&nocoach`);
  await page.waitForSelector(".intro-card", { timeout: 300000 }); await page.waitForTimeout(800);
  await shot("4-intro"); await audit("intro");
  await page.click("[data-act='go']");
  await page.locator("[data-tool='housing']").click().catch(() => {});
  const bs = await page.evaluate(() => window.__sb.blocks());
  const b0 = bs.find((b) => b.p && b.p.x > 0 && b.p.x < W && b.p.y > 0 && b.p.y < H) ?? bs[0];
  if (b0?.p) { await page.mouse.click(b0.p.x, b0.p.y + 10); await page.mouse.move(b0.p.x, b0.p.y + 10); }
  await page.waitForTimeout(1200);
  await shot("5-edit-hover"); await audit("edit+hover");
  await page.keyboard.press("Escape");
  await page.mouse.move(W / 2, 5);
  await page.click("#build", { timeout: 15000 }); await page.waitForFunction(() => window.__sb.isBuilt(), null, { timeout: 300000 }); await page.waitForTimeout(2000);
  await shot("6-built"); await audit("built");
  await page.click("[data-act='close-pc']").catch(() => {});
  for (const l of ["mood", "air"]) { await page.click(`[data-lens='${l}']`).catch(() => {}); await page.waitForTimeout(800); await shot(`7-lens-${l}`); await audit(`lens ${l}`); }
  await page.click("[data-lens='none']").catch(() => {});
  await page.evaluate(() => localStorage.removeItem("sb-revealed-towns"));
  await page.click("#town [data-act='reveal']").catch(() => {});
  await page.waitForTimeout(400); await shot("8-confirm"); await audit("confirm");
  await page.click("[data-act='reveal-yes']").catch(() => {});
  await page.waitForFunction(() => window.__sb.isBuilt(), null, { timeout: 300000 }).catch(() => {}); await page.waitForTimeout(2500);
  await shot("9-solution"); await audit("solution");
  await page.evaluate(() => localStorage.removeItem("sb-revealed-towns"));
  } catch (e) { report.push(`${tag}: FLOW BROKE: ${String(e).split("\n")[0]}`); await shot("x-broken").catch(() => {}); }
  // contact sheet
  const html = `<html><body style="margin:0;background:#333;display:grid;grid-template-columns:repeat(3,1fr);gap:6px;padding:6px">${shots.map(([n, f]) => `<figure style="margin:0;color:#fff;font:12px sans-serif"><img src="file://${f}" style="width:100%;display:block"/>${n}</figure>`).join("")}</body></html>`;
  writeFileSync(`/tmp/sb-shots/resp-${tag}.html`, html);
  const sheet = await browser.newPage({ viewport: { width: 1800, height: 1200 } });
  await sheet.goto(`file:///tmp/sb-shots/resp-${tag}.html`); await sheet.waitForTimeout(500);
  await sheet.screenshot({ path: `/tmp/sb-shots/resp-${tag}.png`, fullPage: true });
  await sheet.close();
  if (errs.length) report.push(`${tag}: page errors ${[...new Set(errs)].slice(0, 2).join(" | ")}`);
  await page.close();
  console.log("done", tag);
}
await browser.close();
console.log(report.length ? report.join("\n") : "NO LAYOUT PROBLEMS FOUND");
