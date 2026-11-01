import { defineConfig } from "vite";

// The browser talks to /ws; Vite forwards it to the bridge (server/bridge.mjs).
const bridge = { "/ws": { target: `ws://localhost:${process.env.BRIDGE_PORT ?? 8787}`, ws: true } };

export default defineConfig({
  server: { port: 5173, proxy: bridge },
  preview: { port: 4173, proxy: bridge },
  build: { chunkSizeWarningLimit: 1200 },
});
