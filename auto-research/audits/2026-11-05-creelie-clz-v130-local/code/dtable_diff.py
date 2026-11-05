#!/usr/bin/env python3
"""dtable_diff.py — locate and quantify value-level differences between two dtable.py outputs.

Layout (little-endian doubles): w lower bounds at grid points [0..L], w'/G lower [L+1..2L+1],
w'/G upper [2L+2..3L+2], w''/G^2 cell lower bounds [3L+3..4L+2].
Usage: python3 dtable_diff.py a.bin b.bin
"""
import struct
import sys

a, b = open(sys.argv[1], "rb").read(), open(sys.argv[2], "rb").read()
assert len(a) == len(b), (len(a), len(b))
n = len(a) // 8
da, db = struct.unpack("<%dd" % n, a), struct.unpack("<%dd" % n, b)
L = (n - 3) // 4
assert 4 * L + 3 == n, "not a dtable.py layout"
segments = [("w(grid)", 0, L + 1), ("w'lo(grid)", L + 1, 2 * L + 2),
            ("w'hi(grid)", 2 * L + 2, 3 * L + 3), ("w''lo(cell)", 3 * L + 3, 4 * L + 3)]
print(f"doubles={n} differing={sum(1 for x, y in zip(da, db) if x != y)}")
worst = 0.0
for i, (x, y) in enumerate(zip(da, db)):
    if x == y:
        continue
    seg, lo, hi = next((s, l, h) for s, l, h in segments if l <= i < h)
    rel = abs(x - y) / max(abs(x), abs(y), 1e-300)
    worst = max(worst, rel)
    print(f"idx={i} {seg}[{i - lo}] shipped={x!r} rebuilt={y!r} absdiff={abs(x - y):.3e} rel={rel:.3e}")
print(f"max_rel_diff={worst:.3e}")
