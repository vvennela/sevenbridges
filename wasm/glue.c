// The C side of the browser build: two functions JavaScript calls.
//   sb_init()          runs the module initializers, once.
//   sb_request(line)   answers one JSON request line with one JSON reply line,
//                      by calling the Lean function `wasmHandle` (Wasm.lean).
// The reply string stays valid until the next call.
#include <lean/lean.h>
#include <emscripten.h>

lean_object * initialize_sevenbridges_Wasm(uint8_t builtin);
lean_object * sb_handle(lean_object * line);   // @[export sb_handle] in Wasm.lean
void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);

// The native program calls `lean_initialize` (from the Lean compiler library,
// `libleancpp`) because SevenBridges.Json imports a module of the `Lean` package.
// That function also starts the elaborator and kernel, which the game never uses,
// so the browser build only starts the runtime. `Init` and every other imported
// module are still started by the module initializers below.
void lean_initialize(void) { lean_initialize_runtime_module(); }

// SevenBridges.Json imports Lean.Elab.Deriving.FromToJson only so that
// `deriving ToJson, FromJson` works at compile time. The game's compiled code
// calls nothing from it (the link fails if it did: its code is not linked), so
// its initializer has nothing to do here.
lean_object * initialize_Lean_Elab_Deriving_FromToJson(uint8_t builtin) {
  return lean_io_result_mk_ok(lean_box(0));
}

static int g_ready = 0;
static lean_object * g_last = NULL;

EMSCRIPTEN_KEEPALIVE int sb_init(void) {
  if (g_ready) return 1;
  lean_initialize_runtime_module();
  lean_object * res = initialize_sevenbridges_Wasm(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 0;
  }
  lean_dec_ref(res);
  g_ready = 1;
  return 1;
}

EMSCRIPTEN_KEEPALIVE const char * sb_request(const char * line) {
  if (!g_ready && !sb_init()) return "{\"ok\":false,\"error\":\"engine failed to start\"}";
  if (g_last) { lean_dec(g_last); g_last = NULL; }
  lean_object * res = sb_handle(lean_mk_string(line));
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return "{\"ok\":false,\"error\":\"engine error\"}";
  }
  g_last = lean_io_result_get_value(res);
  lean_inc(g_last);
  lean_dec_ref(res);
  return lean_string_cstr(g_last);
}
