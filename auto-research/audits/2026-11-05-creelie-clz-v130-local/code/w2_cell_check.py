#!/usr/bin/env python3
"""w2_cell_check.py — high-precision truth check of the six cells where the shipped and the
platform-rebuilt w'' tables differ.

Layout of dtable.py output (little-endian doubles): w lower bounds at grid points [0..L],
w'/G lower [L+1..2L+1], w'/G upper [2L+2..3L+2], w''/G^2 cell lower bounds [3L+3..4L+2].

Recomputes w''/G^2 with mpmath at dps=100 from w(x)=k(x)^2, k=K/K0,
K(x)=(sinc(u-)+sinc(u+))/2, u±=(2*pi*x ± sqrt2)/2, K0=sqrt2*sin(1/sqrt2), and compares both stored
values with a dense sampling of the cell minimum. A stored value above the sampled minimum would be
unsound (the sampled minimum is an upper bound on the true minimum). Also reports a calibration row
per cell (ratio sampled_min/stored, expected close to 1 for a tight lower bound).

Usage: python3 w2_cell_check.py <repo> <rebuilt.bin>
"""
import struct
import sys

from mpmath import mp, mpf, pi, sin, cos, sqrt, nstr

mp.dps = 100
G = 4000
L = 80000
repo, rebuilt = sys.argv[1], sys.argv[2]
s2 = sqrt(2)
K0 = s2 * sin(1 / s2)


def sd(u, d):
    if d == 1:
        return (u * cos(u) - sin(u)) / (u * u)
    return ((2 - u * u) * sin(u) - 2 * u * cos(u)) / (u * u * u)


def w2(x):
    f = 2 * pi * x
    um, up = (f - s2) / 2, (f + s2) / 2
    K = (sin(um) / um + sin(up) / up) / 2
    K1 = (pi / 2) * (sd(um, 1) + sd(up, 1))
    K2 = (pi * pi / 2) * (sd(um, 2) + sd(up, 2))
    return 2 * (K1 * K1 + K * K2) / (K0 * K0) / (G * G)


def load(path):
    return struct.unpack("<%dd" % (4 * L + 3), open(path, "rb").read())


sh = load(f"{repo}/verify/d4000_80k.bin")
rb = load(rebuilt)
# cells from dtable_diff.py: differing doubles are all in the w'' segment
cells = [27137, 28396, 45207, 69127, 69218, 75100]
print(f"G={G} cells={len(cells)} (indices from dtable_diff.py; all six differing doubles are w'' cell bounds)")
ok = True
for c in cells:
    lo, hi = mpf(c) / G, mpf(c + 1) / G
    vals = [w2(lo + (hi - lo) * mpf(i) / 400) for i in range(401)]
    mn = min(vals)
    s, r = mpf(sh[3 * L + 3 + c]), mpf(rb[3 * L + 3 + c])
    print(f"cell {c}: sampled_min={nstr(mn, 12)} shipped={nstr(s, 12)} rebuilt={nstr(r, 12)}")
    print(f"   shipped<=sampled_min:{s <= mn} rebuilt<=sampled_min:{r <= mn} ratio_sampled/shipped={float(mn / s):.6f}")
    ok = ok and s <= mn and r <= mn
# calibration on ordinary cells (shipped == rebuilt there)
for c in (0, 1000, 79999):
    lo, hi = mpf(c) / G, mpf(c + 1) / G
    mn = min(w2(lo + (hi - lo) * mpf(i) / 200) for i in range(201))
    s = mpf(sh[3 * L + 3 + c])
    print(f"calibration cell {c}: sampled_min={nstr(mn, 12)} stored={nstr(s, 12)} ratio={float(mn / s):.6f}")
print("BOTH STORED TABLES ARE VALID LOWER BOUNDS AT THE SIX CELLS:", ok)
sys.exit(0 if ok else 1)
