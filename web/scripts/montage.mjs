// Tile screenshots into one image: node scripts/montage.mjs out.png cols a.png b.png ...
import { chromium } from "playwright";
import { readFileSync } from "node:fs";
const [out, cols, ...files] = process.argv.slice(2);
const c = Number(cols), w = 480, h = 300;
const imgs = files.map((f) => `<div><img src="data:image/png;base64,${readFileSync(f).toString("base64")}"><span>${f.split("/").pop()}</span></div>`).join("");
const browser = await chromium.launch();
const page = await browser.newPage({ viewport: { width: c * w, height: Math.ceil(files.length / c) * h } });
await page.setContent(`<style>body{margin:0;display:grid;grid-template-columns:repeat(${c},${w}px)}div{position:relative;width:${w}px;height:${h}px}img{width:100%;height:100%}span{position:absolute;left:4px;top:2px;font:12px sans-serif;background:#fff}</style>${imgs}`);
await page.screenshot({ path: out });
await browser.close();
