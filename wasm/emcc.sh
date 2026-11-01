#!/bin/bash
# Runs inside the emscripten/emsdk Docker image (called by wasm/build.sh).
# Compiles the Lean runtime, libuv, and every Lean module's C file to WebAssembly
# and links them into out/sevenbridges.mjs + out/sevenbridges.wasm.
#
# Layout of $W (mounted at /work):
#   lean4/   Lean v4.35.0 source (runtime and headers)
#   libuv/   libuv v1.48.0 source
#   c/       C files of every Lean module (core library closure + this project)
#   glue.c   the JavaScript-facing entry points
set -euo pipefail
W=${W:-/work}
J=${JOBS:-$(nproc)}
OPT=${OPT:--O3}
cd "$W"
mkdir -p gen/lean obj/rt obj/c out

# config.h as Lean's CMake writes it, but without mimalloc (Lean's own allocator,
# single-threaded) and for the Emscripten target.
cat > gen/lean/config.h <<'EOF'
#pragma once
#include <lean/version.h>
#define LEAN_IS_STAGE0 0
EOF
sed 's/^#define LEAN_PLATFORM_TARGET .*/#define LEAN_PLATFORM_TARGET "wasm32-unknown-emscripten"/' \
  "$W/version.h" > gen/lean/version.h
echo '#define LEAN_GITHASH ""' > gen/githash.h

COMMON="-DLEAN_EMSCRIPTEN -DNDEBUG -fwasm-exceptions -ffp-contract=off"

# ---- libuv (as Lean's CMake builds it for Emscripten, without threads) ----
if [ ! -f libuv/build/libuv.a ]; then
  ( cd libuv
    grep -q '"Emscripten"' CMakeLists.txt || sed -i 's|^if(CMAKE_SYSTEM_NAME STREQUAL "Linux")$|if(CMAKE_SYSTEM_NAME STREQUAL "Emscripten")\n  list(APPEND uv_sources src/unix/no-proctitle.c)\nendif()\n\nif(CMAKE_SYSTEM_NAME STREQUAL "Linux")|' CMakeLists.txt
    emcmake cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DLIBUV_BUILD_TESTS=OFF -DLIBUV_BUILD_SHARED=OFF \
      -DCMAKE_C_FLAGS="$COMMON" > build.log 2>&1
    cmake --build build -j "$J" >> build.log 2>&1 ) || { tail -40 libuv/build.log; exit 1; }
fi

# ---- the Lean runtime (C++) ----
# v4.35.0's Emscripten stub of this function has the wrong signature; fix it.
sed -i 's/lean_uv_os_get_group() {/lean_uv_os_get_group(uint64_t) {/' lean4/src/runtime/uv/system.cpp
RT=(debug thread mpz utf8 object apply exception interrupt memory stackinfo compact init_module io
    hash byteslice platform alloc allocprof sharecommon stack_overflow process object_ref mpn mutex
    libuv uv/net_addr uv/event_loop uv/timer uv/tcp uv/udp uv/dns uv/system uv/signal openssl)
RTFLAGS="$OPT $COMMON -std=c++20 -DLEAN_EXPORTING -Wno-everything -I gen -I lean4/src -I lean4/src/include -I libuv/include"
printf '%s\n' "${RT[@]}" | xargs -P "$J" -I{} bash -c '
  o=obj/rt/$(echo {} | tr / _).o
  [ "$o" -nt lean4/src/runtime/{}.cpp ] || em++ '"$RTFLAGS"' -c lean4/src/runtime/{}.cpp -o "$o"'

# ---- the Lean modules (C) ----
CFLAGS="$OPT $COMMON -Wno-everything -I gen -I lean4/src/include"
compile_dir() {   # compile_dir SRC_DIR OBJ_DIR: each .c file to a .o file, if out of date
  mkdir -p "$2"
  (cd "$1" && find . -name '*.c' | sed 's|^\./||') | xargs -P "$J" -I{} bash -c '
    o='"$2"'/$(echo {} | tr / _ | sed "s/\.c$/.o/")
    [ "$o" -nt '"$1"'/{} ] || emcc '"$CFLAGS"' -c '"$1"'/{} -o "$o"'
  (cd "$1" && find . -name '*.c' | sed 's|^\./||' | tr / _ | sed "s|^|$2/|; s/\.c$/.o/")
}
compile_dir c obj/c > objs.txt
emcc $CFLAGS -c glue.c -o obj/glue.o

# ---- link ----
# One thread (no SharedArrayBuffer, so plain static hosting works). A large stack
# for the solver's recursion; memory grows as needed. Undefined symbols are an
# error: every function the game calls must be linked. When the game's code calls
# a function compiled in a module that is not linked whole (see extract.py), that
# function is copied from pool/ and the link is tried again.
link() {
  em++ $OPT -fwasm-exceptions obj/glue.o $(cat objs.txt) $(cat xobjs.txt 2>/dev/null) obj/rt/*.o libuv/build/libuv.a \
    -o out/sevenbridges.mjs -Wl,-error-limit=0 \
    -sMODULARIZE=1 -sEXPORT_ES6=1 -sENVIRONMENT=worker,node \
    -sEXPORTED_FUNCTIONS=_sb_init,_sb_request -sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString \
    -sSTACK_SIZE=${STACK:-64MB} -sINITIAL_MEMORY=${MEM:-256MB} -sALLOW_MEMORY_GROWTH=1 -sMAXIMUM_MEMORY=4GB \
    -sERROR_ON_UNDEFINED_SYMBOLS=1 -sEXIT_RUNTIME=0 -sFILESYSTEM=1
}
: > roots.txt
for round in 1 2 3 4 5 6 7 8; do
  if link > link.log 2>&1; then break; fi
  sed -n 's/.*undefined symbol: //p' link.log | sort -u > undef.txt
  if [ ! -s undef.txt ] || [ "$round" = 8 ]; then cat link.log; exit 1; fi
  sort -u roots.txt undef.txt -o roots.txt
  echo "link round $round: copying $(wc -l < undef.txt) functions from pool/"
  rm -rf extract && python3 extract.py extract pool $(cat roots.txt)
  compile_dir extract obj/x > xobjs.txt
done
grep -v "function signature mismatch\|defined as\|^$" link.log || true
ls -la out
