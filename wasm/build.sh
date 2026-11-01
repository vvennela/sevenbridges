#!/bin/bash
# Build the browser engine: the same Lean backend code as the native program
# (SevenBridges/Backend.lean), compiled to WebAssembly.
#
#   wasm/build.sh            -> web/public/engine/sevenbridges.{mjs,wasm}
#
# Needs: elan (Lean 4.35.0), python3, curl, Docker (emscripten/emsdk image).
# Work files go to $SB_WASM_WORK (default /tmp/sevenbridges-wasm).
#
# Steps:
#  1. Lake writes the C file of each project module that Wasm.lean imports.
#  2. The toolchain's `lean -c` writes the C file of each core library module
#     those import (Init, and the Std/Lean modules under Lean.Data.Json). This
#     is the same compiler, on the same sources, that made the native libraries.
#  3. Emscripten compiles them with the Lean runtime (from the v4.35.0 source)
#     and links one .wasm module (wasm/emcc.sh).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/.." && pwd)
W=${SB_WASM_WORK:-/tmp/sevenbridges-wasm}
LEAN_VERSION=4.35.0
LIBUV_VERSION=1.48.0
EMSDK_VERSION=4.0.10
case "$(uname -m)" in arm64|aarch64) EMSDK_IMAGE=${EMSDK_IMAGE:-emscripten/emsdk:$EMSDK_VERSION-arm64} ;;
  *) EMSDK_IMAGE=${EMSDK_IMAGE:-emscripten/emsdk:$EMSDK_VERSION} ;; esac
export PATH="$HOME/.elan/bin:$PATH"
TC=$(cd "$ROOT" && lean --print-prefix)
mkdir -p "$W"

# ---- sources ----
if [ ! -d "$W/lean4/src/runtime" ]; then
  curl -sSL "https://codeload.github.com/leanprover/lean4/tar.gz/refs/tags/v$LEAN_VERSION" -o "$W/lean4.tar.gz"
  mkdir -p "$W/lean4" && tar xzf "$W/lean4.tar.gz" -C "$W/lean4" --strip-components=1 "lean4-$LEAN_VERSION/src"
fi
if [ ! -f "$W/libuv/CMakeLists.txt" ]; then
  curl -sSL "https://codeload.github.com/libuv/libuv/tar.gz/refs/tags/v$LIBUV_VERSION" -o "$W/libuv.tar.gz"
  mkdir -p "$W/libuv" && tar xzf "$W/libuv.tar.gz" -C "$W/libuv" --strip-components=1
fi
cp "$TC/include/lean/version.h" "$W/version.h"
cp "$HERE/glue.c" "$HERE/emcc.sh" "$W/"

# ---- 1. project modules ----
cd "$ROOT"
lake build Wasm >/dev/null
python3 -I "$HERE/imports.py" "$ROOT" Wasm 2>"$W/external.txt" > "$W/project.txt"
lake build $(sed 's/^/+/; s/$/:c/' "$W/project.txt") >/dev/null
mkdir -p "$W/c"
while read -r m; do
  p=${m//.//}
  mkdir -p "$W/c/$(dirname "$p")"
  cmp -s ".lake/build/ir/$p.c" "$W/c/$p.c" || cp ".lake/build/ir/$p.c" "$W/c/$p.c"
done < "$W/project.txt"

# ---- 2. core library modules ----
# Linked whole: Init and the modules under Lean.Data.Json (all that the game's
# code needs). Lean.Elab.Deriving.FromToJson is imported only for `deriving
# ToJson` at compile time; its modules go to pool/, from which wasm/extract.py
# copies the few compiled functions the game's code reuses (see extract.py).
ext=$(sed -n 's/^MISSING //p' "$W/external.txt")
python3 -I "$HERE/imports.py" "$TC/src/lean" Init $(echo "$ext" | grep -vx 'Lean.Elab.Deriving.FromToJson') > "$W/core.txt"
python3 -I "$HERE/imports.py" "$TC/src/lean" Init $ext | grep -vxF -f "$W/core.txt" > "$W/pool.txt" || true
echo "core modules: $(wc -l < "$W/core.txt"), pool modules: $(wc -l < "$W/pool.txt"), project modules: $(wc -l < "$W/project.txt")"
emit() {   # emit DIR MODULE
  p=${2//.//}
  [ -f "$W/$1/$p.c" ] && return 0
  mkdir -p "$W/$1/$(dirname "$p")"
  (cd "$TC/src/lean" && "$TC/bin/lean" -R . -c "$W/$1/$p.c.tmp" "$p.lean" >/dev/null) && mv "$W/$1/$p.c.tmp" "$W/$1/$p.c"
}
export -f emit; export W TC
xargs -P 8 -I{} bash -c 'emit c {}' < "$W/core.txt"
xargs -P 8 -I{} bash -c 'emit pool {}' < "$W/pool.txt"
cp "$HERE/extract.py" "$W/"

# ---- 3. Emscripten ----
docker run --rm -v "$W:/work" -e OPT -e STACK -e MEM "$EMSDK_IMAGE" bash /work/emcc.sh

mkdir -p "$ROOT/web/public/engine"
cp "$W/out/sevenbridges.mjs" "$W/out/sevenbridges.wasm" "$ROOT/web/public/engine/"
ls -la "$ROOT/web/public/engine"
