"""Print every module that the given modules import, directly or not, found
under ROOT. Usage: python3 imports.py ROOT MODULE...

Missing modules (for example ones from another root) are printed to stderr
as "MISSING name" and not followed."""
import os
import re
import sys

root = sys.argv[1]
todo = sys.argv[2:]
seen = set()
pat = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)
while todo:
    m = todo.pop()
    if m in seen:
        continue
    p = os.path.join(root, *m.split('.')) + '.lean'
    if not os.path.exists(p):
        print('MISSING', m, file=sys.stderr)
        continue
    seen.add(m)
    src = re.sub(r'/-.*?-/', '', open(p, encoding='utf-8').read(), flags=re.S)
    todo.extend(pat.findall(src))
for m in sorted(seen):
    print(m)
