#!/usr/bin/env python3
"""Independent re-derivation of the N=4 certificate for H >= 269/400.

Recomputes, in exact rational arithmetic (fractions.Fraction) and 60-digit
decimals, every quantity the audited package asserts:

  A   = sin(u)/u = sum_{j>=0} (-1)^j (1/2)^j / (2j+1)!      u = 1/sqrt(2)
  B   = cos(u)   = sum_{j>=0} (-1)^j (1/2)^j / (2j)!
  s   = u*tan(u) = A/(2B)
  cMT = 2s/(1+s)
  H   = 2 - 1/cMT = 3/2 - (1/sqrt2)*cot(1/sqrt2)

and checks the chain the package proves:

  331*A >= 400*B  =>  s >= 200/331  =>  cMT >= 400/531  =>  H >= 269/400

It also enumerates all 9 sign orientations of the two alternating-series
remainders, to show that the package's claimed margin 821/5806080 is the
CORRECT (conservative) orientation and that its documented "direction trap"
value 8683/5806080 is exactly the flipped one.

No network access. No Lean toolchain needed. Run: python3 verify.py

Reference implementation: mpmath is used for the transcendental cross-checks
when available (it is not required -- the exact-rational checks stand alone).
"""
import math
import sys
from fractions import Fraction as F
from decimal import Decimal, getcontext

getcontext().prec = 60

try:
    import mpmath
    mpmath.mp.dps = 60
except ImportError:  # optional
    mpmath = None

FAILURES = []
TOL = Decimal("1e-50")


def check(name, cond, detail=""):
    status = "PASS" if cond else "FAIL"
    print(f"[{status}] {name}" + (f"  -- {detail}" if detail else ""))
    if not cond:
        FAILURES.append(name)
    return cond


def partial_A(n):
    """N-term partial sum of sin(u)/u = sum (-1)^j (1/2)^j / (2j+1)!."""
    return sum((-1) ** j * F(1, 2 ** j) / F(math.factorial(2 * j + 1)) for j in range(n))


def partial_B(n):
    """N-term partial sum of cos(u) = sum (-1)^j (1/2)^j / (2j)!."""
    return sum((-1) ** j * F(1, 2 ** j) / F(math.factorial(2 * j)) for j in range(n))


def main():
    # ---- 1. the certificate constants are really the N=4 partial sums ----
    A4, B4 = F(37043, 40320), F(4379, 5760)
    A_err, B_err = F(1, 5806080), F(1, 645120)
    check("A_part == 4-term partial of sin(u)/u series", A4 == partial_A(4))
    check("B_part == 4-term partial of cos(u) series", B4 == partial_B(4))
    check("A_err == first omitted A term", A_err == F(1, 16) / F(math.factorial(9)))
    check("B_err == first omitted B term", B_err == F(1, 16) / F(math.factorial(8)))

    # ---- 2. the conservative margin is exactly 821/5806080 ----
    margin = 331 * (A4 - A_err) - 400 * (B4 + B_err)
    check("margin == 821/5806080", margin == F(821, 5806080), str(margin))
    check("margin > 0", margin > 0, f"{float(margin):.6e}")

    # ---- 3. the documented direction trap is the flipped orientation ----
    flipped = 331 * (A4 + A_err) - 400 * (B4 - B_err)
    check("flipped orientation == 8683/5806080", flipped == F(8683, 5806080), str(flipped))
    check("flipped/true ratio == 10.576...", abs(flipped / margin - 10.576127) < 1e-5,
          f"{float(flipped / margin):.6f}")
    combos = {}
    for na in (0, 1, -1):
        for nb in (0, 1, -1):
            combos[(na, nb)] = 331 * (A4 + na * A_err) - 400 * (B4 + nb * B_err)
    check("821/5806080 arises only from (A-A_err, B+B_err)",
          [k for k, v in combos.items() if v == F(821, 5806080)] == [(-1, 1)])
    check("8683/5806080 arises only from (A+A_err, B-B_err)",
          [k for k, v in combos.items() if v == F(8683, 5806080)] == [(1, -1)])

    # ---- 4. the chain, at 60 digits ----
    u = (Decimal(1) / Decimal(2)).sqrt()
    Aex = sum(((-1) ** j) * (Decimal(1) / (Decimal(2) ** j)) / Decimal(math.factorial(2 * j + 1))
              for j in range(30))
    Bex = sum(((-1) ** j) * (Decimal(1) / (Decimal(2) ** j)) / Decimal(math.factorial(2 * j))
              for j in range(30))
    sin_u = u * Aex          # sin(u) = u * A exactly, since A = sin(u)/u
    s = Aex / (2 * Bex)      # s = u*tan(u) = u*sin(u)/cos(u) = u^2 * A/B = (1/2) A/B
    cMT = 2 * s / (1 + s)
    H = 2 - 1 / cMT

    # 4a. internal consistency of the two series, independent of any reference:
    #     sin(u)^2 + cos(u)^2 = 1
    pyth = sin_u * sin_u + Bex * Bex
    check("sin(u)^2 + cos(u)^2 == 1 (series self-consistency)", abs(pyth - 1) < Decimal("1e-55"),
          f"|sum-1| = {abs(pyth - 1)}")

    # 4b. the identity s = u*tan(u) = A/(2B), which uses u^2 = 1/2 exactly
    s_via_u = u * sin_u / Bex
    check("s == u*sin(u)/cos(u) == A/(2B)", abs(s_via_u - s) < Decimal("1e-55"),
          f"|diff| = {abs(s_via_u - s)}")

    # 4c. cross-check the series against an independent transcendental reference
    if mpmath is not None:
        um = mpmath.mpf(1) / mpmath.sqrt(2)
        check("sin(u) matches mpmath.sin(1/sqrt2)",
              abs(mpmath.sin(um) - mpmath.mpf(str(sin_u))) < mpmath.mpf("1e-55"))
        check("cos(u) matches mpmath.cos(1/sqrt2)",
              abs(mpmath.cos(um) - mpmath.mpf(str(Bex))) < mpmath.mpf("1e-55"))
        check("s matches mpmath u*tan(u)",
              abs(mpmath.mpf(um) * mpmath.tan(um) - mpmath.mpf(str(s))) < mpmath.mpf("1e-55"))
    else:
        print("[SKIP] mpmath unavailable -- transcendental cross-checks skipped "
              "(exact-rational checks above are unaffected)")

    # 4d. the chain inequalities
    check("331A - 400B > 0", 331 * Aex - 400 * Bex > 0, f"{331 * Aex - 400 * Bex}")
    check("s > 200/331", s - Decimal(200) / Decimal(331) > 0, f"{s - Decimal(200) / Decimal(331)}")
    check("cMT > 400/531", cMT - Decimal(400) / Decimal(531) > 0,
          f"{cMT - Decimal(400) / Decimal(531)}")
    check("H - 269/400 > 0", H - Decimal(269) / Decimal(400) > 0,
          f"{H - Decimal(269) / Decimal(400)}")
    check("H == 2 - 1/cMT", abs(H - (2 - 1 / cMT)) < TOL)
    check("2 - 531/400 == 269/400 exactly", F(2) - F(531, 400) == F(269, 400))

    print()
    print("cMT =", cMT)
    print("H   =", H)
    print("H - 269/400 =", H - Decimal(269) / Decimal(400))

    print()
    if FAILURES:
        print(f"FAILED {len(FAILURES)} check(s): {FAILURES}")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
