import { defineConfig } from "vite";

// With `?server`, the browser talks to /ws; Vite forwards it to the bridge (server/bridge.mjs).
const bridge = { "/ws": { target: `ws://localhost:${process.env.BRIDGE_PORT ?? 8787}`, ws: true } };

export default defineConfig(({ command, isPreview }) => ({
  // GitHub Pages serves the game at https://vvennela.github.io/sevenbridges/
  base: process.env.SB_BASE ?? (command === "build" || isPreview ? "/sevenbridges/" : "/"),
  server: { port: 5173, proxy: bridge, fs: { allow: [".."] } },
  preview: { port: 4173, proxy: bridge },
  worker: { format: "es" },
  build: { chunkSizeWarningLimit: 1200 },
}));
