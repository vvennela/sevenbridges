"""Copy single compiled functions out of Lean's C files.

Why: when Lean compiles a function, it reuses specialized copies of generic
functions (for example `Json.getObjValAs?` at type `String`) that an imported
module already made. SevenBridges.Json imports Lean.Elab.Deriving.FromToJson
(for `deriving ToJson`), so a few of these copies live in modules of the Lean
compiler (Lean.Data.Lsp.Basic, Lean.SubExpr, ...). Linking those whole modules
would pull in the whole compiler. Instead this script copies, unchanged, just
the functions the game's code calls, and what they need from the same file.

It refuses to copy anything that is set up at run time by a module initializer
(the copy would be missing its value), so a copy behaves exactly as the original.

Usage: python3 extract.py OUT_DIR POOL_DIR SYMBOL...
  POOL_DIR holds the C files to search (any depth). Writes one C file per
  source module into OUT_DIR, named after the module, with `extract_` in front.
"""
import os
import re
import sys

IDENT = re.compile(r'\b(l_[A-Za-z0-9_]+|lp_[A-Za-z0-9_]+)\b')


def items(src):
    """Split a C file from Lean's compiler into top-level items.
    Returns a list of (kind, name, text): kind is 'pp', 'decl', 'data', 'func'."""
    out = []
    i, n = 0, len(src)
    while i < n:
        if src[i] in ' \t\n':
            i += 1
            continue
        if src[i] == '#':
            j = src.index('\n', i)
            out.append(('pp', None, src[i:j + 1]))
            i = j + 1
            continue
        if src[i] == '}':   # end of `extern "C" {` under #ifdef __cplusplus
            out.append(('pp', None, '}\n'))
            i += 1
            continue
        if src.startswith('extern "C" {', i):   # under #ifdef __cplusplus
            out.append(('pp', None, 'extern "C" {\n'))
            i += len('extern "C" {')
            continue
        if src.startswith('//', i):
            i = src.index('\n', i) + 1
            continue
        # scan one item: up to ';' at depth 0, or the '}' that closes a function body
        depth, j, in_str, saw_eq = 0, i, False, False
        while True:
            c = src[j]
            if in_str:
                if c == '\\':
                    j += 2
                    continue
                if c == '"':
                    in_str = False
            elif c == '"':
                in_str = True
            elif c == '{':
                depth += 1
            elif c == '}':
                depth -= 1
                if depth == 0 and not saw_eq:
                    j += 1
                    break
            elif c == '=' and depth == 0:
                saw_eq = True
            elif c == ';' and depth == 0:
                j += 1
                break
            j += 1
        text = src[i:j]
        head = text.split('{', 1)[0] if not saw_eq else text.split('=', 1)[0]
        if text.rstrip().endswith('}') and not saw_eq:
            kind = 'func'
            name = re.search(r'([A-Za-z0-9_]+)\s*\(', head).group(1)
        elif saw_eq:
            kind = 'data'
            name = re.findall(r'([A-Za-z0-9_]+)\s*(?:\[\])?\s*$', head.strip())[0]
        else:
            kind = 'decl'
            m = re.search(r'([A-Za-z0-9_]+)\s*\(', text)
            name = m.group(1) if m else re.findall(r'([A-Za-z0-9_]+)\s*;\s*$', text)[0]
        out.append((kind, name, text))
        i = j
    return out


def extract(path, roots):
    src = open(path, encoding='utf-8').read()
    its = items(src)
    defs = {}
    for k, name, text in its:
        if k in ('func', 'data'):
            defs[name] = text
    runtime_init = {name for k, name, text in its if k == 'func' and name.startswith('_init_')}
    need, todo = set(), list(roots)
    while todo:
        s = todo.pop()
        if s in need:
            continue
        if '_init_' + s in runtime_init:
            raise SystemExit(f'{path}: {s} is set up at run time; cannot copy it')
        if s not in defs:
            continue   # defined in another module
        need.add(s)
        for r in IDENT.findall(defs[s]):
            if r != s:
                todo.append(r)
    missing = [r for r in roots if r not in need]
    if missing:
        raise SystemExit(f'{path}: not defined here: {missing}')
    kept = []
    for k, name, text in its:
        if k == 'pp' or k == 'decl':
            if k == 'decl' and '_init_' + name in runtime_init:
                continue
            kept.append(text if text.endswith('\n') else text + '\n')
        elif name in need:
            kept.append(text + '\n')
    return ''.join(kept), sorted(need)


def main():
    out, pool, syms = sys.argv[1], sys.argv[2], sys.argv[3:]
    files = []
    for d, _, fs in os.walk(pool):
        files += [os.path.join(d, f) for f in fs if f.endswith('.c')]
    by_file = {}
    for s in syms:
        pat = re.compile(r'^(?:LEAN_EXPORT |static )?[^\n;=]*\b' + re.escape(s) + r'\b[^\n;]*\{', re.M)
        hits = [f for f in files if s in open(f, encoding='utf-8').read() and pat.search(open(f, encoding='utf-8').read())]
        if len(hits) != 1:
            raise SystemExit(f'{s}: defined in {len(hits)} files of the pool: {hits}')
        by_file.setdefault(hits[0], []).append(s)
    os.makedirs(out, exist_ok=True)
    for f, roots in sorted(by_file.items()):
        text, need = extract(f, roots)
        rel = os.path.relpath(f, pool)
        print(f'{rel}: copied {len(need)} definitions for {len(roots)} symbols', file=sys.stderr)
        name = 'extract_' + rel.replace(os.sep, '_')
        with open(os.path.join(out, name), 'w', encoding='utf-8') as h:
            h.write(f'// Copied unchanged from {rel} by wasm/extract.py; do not edit.\n'
                    f'// Definitions: {" ".join(need)}\n' + text)


if __name__ == '__main__':
    main()
