#!/usr/bin/env python3
"""controls_mpmath.py — exact-arithmetic checks of the v1.3.0 claim (mpmath, 60 digits).

Runs the identity that turns the certified window inequality into the claimed bound, checks the
displayed digits against the exact value, checks the paper's condition (eq:c0cond), and checks the
weights file's linear total. Prints every number at 60 significant digits.
"""
import sys

from mpmath import mp, mpf, cot, sqrt, sin, cos, nstr

mp.dps = 60

# H = 3/2 - cot(1/sqrt2)/sqrt2, the paper's Montgomery-Taylor constant
H = mpf(3) / 2 - cot(1 / sqrt(2)) / sqrt(2)
mu = mpf(7999) / 2000000
c0 = mpf(889) / 125000
bound = (H - mu) / (1 - c0)
closed = (mpf(125000) / 124111) * (H - mu)

print("H              =", nstr(H, 60))
print("mu (linear)    =", nstr(mu, 40), "= 7999/2000000 (exact)")
print("c0 (certified) =", nstr(c0, 40), "= 889/125000 (exact)")
print("1 - c0         =", nstr(1 - c0, 40), "= 124111/125000 (exact)")
print("bound (H-mu)/(1-c0)        =", nstr(bound, 60))
print("bound (125000/124111)(H-mu)=", nstr(closed, 60))
print("closed form equals quotient:", abs(bound - closed) < mpf(10) ** -55)
print("paper's printed 16 digits  = 0.6732896395962199 (truncation) ; exact =", nstr(bound, 20))
print("claimed board-style 10 dp  = 0.6732896395")
print("10-dp truncation           =", nstr(mpf(int(bound * 10 ** 10)) / 10 ** 10, 12))
print("10-dp correct rounding     =", nstr(mpf(round(bound * 10 ** 10)) / 10 ** 10, 12))
print("claimed <= exact (a true lower bound remains claimed):", mpf("0.6732896395") <= bound)

# paper's condition (eq:c0cond): 11 c0 < 0.4794 < (4/3) w(11/20), w = k^2
def k(x):
    return (sin(sqrt(2) / 2 - mp.pi * x) / (sqrt(2) / 2 - mp.pi * x)
            + sin(sqrt(2) / 2 + mp.pi * x) / (sqrt(2) / 2 + mp.pi * x)) / 2 / (sqrt(2) * sin(1 / sqrt(2)))


w11_20 = k(mpf(11) / 20) ** 2
print("11*c0          =", nstr(11 * c0, 20))
print("0.4794         = 0.4794")
print("(4/3) w(11/20) =", nstr(mpf(4) / 3 * w11_20, 30))
print("condition 11c0 < 0.4794 < (4/3)w(11/20):", 11 * c0 < mpf("0.4794") < mpf(4) / 3 * w11_20)

# weights file linear total and certified target
from fractions import Fraction

total = Fraction(0)
weights_path = sys.argv[1] if len(sys.argv) > 1 else "verify/weights10.txt"
for line in open(weights_path):
    p = line.split()
    if p and p[0] == "b":
        total += Fraction(int(p[2]), int(p[3]))
print(f"sum of b_i in {weights_path} =", total, "==", Fraction(7999, 2000000), total == Fraction(7999, 2000000))
print("F target 889/125000 =", nstr(c0, 20), "; 0.0071125 =", nstr(mpf("0.0071125"), 10), "; margin =", nstr(c0 - mpf("0.0071125"), 6))

# ceilings
print("ten-zero weight ceiling (chain_window10.txt) = 0.6732908 ; claim below ceiling:", bound < mpf("0.6732908"))
print("method ceiling (chain_all.txt) = 0.6735602 <= 0.67357:", mpf("0.6735602") <= mpf("0.67357"))
print("row gain over listed v1.0.0 0.6731134:", nstr(bound - mpf("0.6731134"), 10))
