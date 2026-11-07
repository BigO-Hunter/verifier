#!/usr/bin/env python3
"""Independent exact-arithmetic recomputation of the mu(G) <= 295 criterion chain.
All inputs are the exact Lean literals from CatalanMeasure/GenD/Signed/RouteI/Literals.lean
and DesignInstance/PositiveBudget.lean (K590.target). No floats anywhere except display."""
from fractions import Fraction as F
import decimal
decimal.getcontext().prec = 220
D = decimal.Decimal

# --- Lean literals (exact) ---
cost296   = F(3596893, 1000000)
psi296    = F(8723, 100)
rho296    = 58 * cost296 + psi296
delta296  = F(29, 10**8)
shift296  = F(57783, 2500)
content295= F(220607, 10000)
eta295    = F(798775, 100000) + content295 + shift296 - F(1, 1000)
K590target= F(563964709, 250000000)
T296      = K590target + shift296 / (58**2)
content296= F(0x33b226df05efafb7e3, 0x25c6ecd580a48ba00)
eta296    = F(798775, 100000) + content296 + shift296 - F(1, 1000)

def show(name, x):
    d = D(x.numerator) / D(x.denominator)
    print(f"{name:12s} = {x}  = {d}")

show("rho296", rho296);  print("   README rho = 295.849794  ->", "MATCH" if rho296 == F(147924897,500000) and abs(D(rho296.numerator)/D(rho296.denominator) - D("295.849794")) < D(10)**-9 else "MISMATCH")
show("delta296", delta296)
show("eta295", eta295);  print("   README eta = 53.16065     ->", "MATCH" if abs(D(eta295.numerator)/D(eta295.denominator) - D("53.16065")) < D(10)**-9 else "MISMATCH")
show("T296", T296)
show("content296(hex)", content296)
show("eta296", eta296)

# --- Criterion: B=295 must clear d*rho/(eta - 4*d*delta), d=53 (README) ---
d = 53; B = 295
lhs_num = d * rho296
denom   = eta295 - 4 * d * delta296
crit    = F(lhs_num, 1) / denom
print()
print("criterion  d*rho/(eta-4ddelta) with d=53:")
show("  numerator d*rho", lhs_num)
show("  denom eta-4dδ", denom)
show("  quotient", crit)
print(f"  B=295 > quotient ? -> {B > crit}   (margin = {D(B) - D(crit.numerator)/D(crit.denominator)})")
print(f"  README claims quotient = 294.956...  -> recomputed {D(crit.numerator)/D(crit.denominator)}")

# exact product form (what Lean would decide): B*(eta-4dδ) > d*rho ?
prod_lhs = B * denom
print(f"  exact: 295*(eta-4dδ) - 53*rho = {prod_lhs - lhs_num} = {float(prod_lhs - lhs_num):.6f} > 0")

# --- Hybrid table cross-checks (gamma/(D-Lambda), rounding discipline) ---
print()
rows = [
    ("G±5pi2/48",      F(71904273,10**7), F(37447213,10**7), F(35149036,10**7), F(312876,10**4)),
    ("L(2,chi-3)",     F(75043742,10**7), F(46435117,10**7), F(40959278,10**7), F(137046,10**4)),
    ("L±pi2/9",        F(68272548,10**7), F(40291249,10**7), F(33104458,10**7), F(94998,10**4)),
    ("psi'(a/5)-z2",   F(71655663,10**7), F(38135797,10**7), F(35128488,10**7), F(238272,10**4)),
    ("psi'(a/7)-z2",   F(74259546075,10**10), F(36424792669,10**10), F(36391158643,10**10), F(22078697,10**4)),
    ("pi2",            F(64350874,10**7), F(39785713,10**7), F(29923824,10**7), F(65253,10**4)),
]
for name, g, Dc, L, Bb in rows:
    q = g / (Dc - L)
    qd = D(q.numerator)/D(q.denominator)
    Bd = D(Bb.numerator)/D(Bb.denominator)
    ok = q <= Bb
    print(f"{name:14s} gamma/(D-L) = {qd:.7f}  board B = {Bd}  quotient <= B ? {ok}")
