# Audit: `H >= 269/400` for the critical-line-zeros row (local replay)

Independent audit of the Lean proof package
[`darkhipo/critical-line-269-400`](https://github.com/darkhipo/critical-line-269-400)
at commit `ac06cb570f` (published 2026-11-05T00:13Z).

**Verdict: no row-invalidating discrepancy.** The certificate is arithmetically
correct, the two analytic plugs rest on the right Mathlib lemmas with the right
indices, the build receipt is authentic, and the package's own stated limit
(the proof-library port to the verifier's site pins is unmeasured) is accurate.
One disclosure gap, recorded below; it is a limit, not a defect.

## What the audited package claims

The `critical-line-zeros` board scores
`kappa* = liminf_{T->inf} N0simple(T)/N(T)` (simple zeros on the critical line,
zeros with multiplicity, `0 < Im rho <= T`; **higher is better**). The board's
Anthropic-breakthrough row is the constant

    H = 3/2 - (1/sqrt2)*cot(1/sqrt2) = 2 - 1/cMT = 0.6725007036794116457...

The package proves `H >= 269/400 = 0.6725` in Lean (margin `7.04e-7`), and
bridges it to the board's adapter shape:

    Race.bound (269/400 : Q)  :=  forall eps > 0, exists T0, forall T >= T0,
                                  (269/400 - eps) * N(T) <= N0simple(T)

## What this audit did

Read-only, no rebuild, no network-heavy Lean build. Every number below was
recomputed here in exact rational arithmetic (`fractions.Fraction`) and at 60
decimal digits, independently of the audited package.

### 1. The N=4 certificate is exactly what it claims

With `u = 1/sqrt2`, so `u^2 = 1/2` exactly and every series term is an exact
rational:

    A = sin(u)/u = sum_{j>=0} (-1)^j (1/2)^j / (2j+1)!
    B = cos(u)   = sum_{j>=0} (-1)^j (1/2)^j / (2j)!

| constant | value | verified as |
|---|---|---|
| `A_part` | `37043/40320` | the 4-term partial sum of `A` -- exact match |
| `B_part` | `4379/5760` | the 4-term partial sum of `B` -- exact match |
| `A_err` | `1/5806080` | the first omitted `A` term -- exact match |
| `B_err` | `1/645120` | the first omitted `B` term -- exact match |

The conservative margin is therefore exactly

    331*(A_part - A_err) - 400*(B_part + B_err) = 821/5806080 > 0

which is the value the package states.

### 2. The documented direction trap is real and correctly characterised

The package warns that flipping the orientation of the two remainder bounds
yields `+8683/5806080`, "10.58x the true margin", and would typecheck while
proving nothing. Enumerating all 9 sign combinations of `(A +- A_err)` and
`(B +- B_err)` shows each claimed value arises from exactly one orientation:

| orientation | margin | |
|---|---|---|
| `(A - A_err, B + B_err)` | `821/5806080` | the correct conservative one |
| `(A + A_err, B - B_err)` | `8683/5806080` | the trap; ratio `8683/821 = 10.576127` |

The warning is accurate, and the package's choice is the sound one.

### 3. The chain holds, at 60 digits

    A      = 0.918725369865568437784231525124661751810172479994571608598353
    B      = 0.760244597075630151253547198623274394617583171135131208568029
    s      = u*tan(u) = A/(2B) = 0.604230121068635760976997386112151653041922950024156731611230
    cMT    = 2s/(1+s)   = 0.753296067856070677216584628269727682295739559906198738568757
    H      = 2 - 1/cMT  = 0.672500703679411645734379790803295188593403028626264078929589

Every step of `331A >= 400B => s >= 200/331 => cMT >= 400/531 => H >= 269/400`
is positive:

| gap | value |
|---|---|
| `331A - 400B` | `2.5859525109240516e-4` |
| `s - 200/331` | `5.1381788047396793e-7` |
| `cMT - 400/531` | `3.9930616483917515e-7` |
| `H - 269/400` | `7.0367941164573438e-7` |

and the boundary is exact: `2 - 531/400 = 269/400`. Two independent
consistency checks also hold: `sin(u)^2 + cos(u)^2 = 1` to within `0E-59`, and
`s = u*sin(u)/cos(u) = A/(2B)` to within `2E-60` (the second uses `u^2 = 1/2`
exactly).

### 4. Package integrity

All four published Lean files hash exactly to the values in the package's own
`receipts/shasums.txt`:

| file | sha256 |
|---|---|
| `lean/HGe269.lean` | `f2069375b84571760513f84761d4cac09675609d2f0371ee3df01e0471ceed94` |
| `lean/Bridge269.lean` | `1a12497d09aebf143e7566b70fe29e61800e85219f57f566e2dea22d9a008410` |
| `lean/P2Plugs.lean` | `7fb821c4383da1d85bee8aa5da037312c4ef2da8d54a5fd268868455bd1da763` |
| `lean/adapter/RaceBound.lean` | `1d98d747f01f98b49ef37a1681c8a4f845099c871eedf2b8f2871b3bf0b42ad4` |

### 5. The build receipt is authentic (falsifiable check)

Rather than trusting `receipts/build-final.log`, each of its 20
`depends on axioms` entries was re-located by **line number** in the
**published** sources. All 20 match on all three counts: the line number, the
declared theorem name, and the axiom set being exactly
`[propext, Classical.choice, Quot.sound]`. The log contains zero `sorry` and
zero `error` lines and ends with `Build completed successfully (8890 jobs)`.

A synthesised log would not carry per-line offsets consistent with the
published files, so the receipt is a real build log of these sources.
See `evidence/receipt-line-authenticity.txt`.

### 6. The Mathlib lemmas were read at the pin, not assumed

The two analytic plugs rest on Mathlib's Leibniz partial-sum bounds. The
auditor fetched `Mathlib/Analysis/SpecificLimits/Normed.lean` **at the pinned
commit** `51e6992efd06126df61a496bebf8f49482a4e129` and read:

    Antitone.alternating_series_le_tendsto ... : (sum i in range (2*k),   (-1)^i * f i) <= l
    Antitone.tendsto_le_alternating_series ...: l <= (sum i in range (2*k+1), (-1)^i * f i)

The package uses `k = 2` and states `range 4` (lower) and `range 5` (upper) --
exactly right. This is the load-bearing detail: an off-by-one here would make
the whole certificate vacuous, and the `range 5` upper bound in particular is
easy to get wrong. The plugs are semantically sound, not merely type-correct.
See `evidence/mathlib-Normed-at-pin.txt`.

### 7. The zeta23 interface matches the source

Checked against `anthropics/formal-math` at `16a5ce41`:

- `ChallengeDeps.cMT = sqrt2*tan(1/sqrt2)/(1 + (1/sqrt2)*tan(1/sqrt2))` -- as claimed.
- `Ncount`, `N0simple`, `zerosIn`, `zeroMult` are defined as claimed, and
  `N0simple` counts simple zeros on the critical line with multiplicity
  excluded -- matching the board quantity.
- `Solution.montgomery_taylor_simple_on_critical_line_mult_cumulative` exists
  and has exactly the epsilon-form shape the bridge consumes.
- `Zeta23.ThmD.thmD0_simple_mult_cumulative` is
  `forall eps > 0, exists T0, forall T >= T0, (HD 1 - eps) * (Ncount 0 T) <= N0simple 0 T`
  -- exactly the shape `Bridge269.lean` uses.
- `Zeta23.ThmD.HD_one` is `HD 1 = 3/2 - (sqrt 2)^-1 * (cos (sqrt 2)^-1 / sin (sqrt 2)^-1)`,
  i.e. the page form the package targets.

The package's identity `H_eq` (page form `= 2 - 1/cMT`) re-derives the same
identity zeta23 itself uses, via `Solution.cStar_one_eq_cMT`. It is therefore
a re-derivation of a known identity, not an independent claim -- consistent
with the package's own credit note.

## The one disclosure gap (a limit, not a defect)

**The port of the 316-module proof library to the verifier's site pins is
unmeasured.** The package builds at zeta23's *native* pins (Lean
`v4.33.0-rc2`, Mathlib `51e6992e`). The verifier site runs Lean `v4.34.1` +
Mathlib `d13f23b7`. The package's own `NOTICE.md` states this limit, and it is
correct: only the statement surface was verified to compile unmodified at the
site pins.

## Board state (measured)

The route is **cold**, so this proof cannot become a Lean Verified row yet:

- no `challenges/critical-line-zeros/` in the verifier tree;
- `profiles/direct.json` has no `critical-line-zeros` key;
- the site's `src/lib/other-bounds.json` has no `critical-line-zeros` family;
- the site's `data/direct-other.json` has no `other-critical-line-zeros` board.

This matches the maintainer's answer on issue #146 (2026-11-04T20:57Z): the
maintainers plan the route themselves, will write the trusted statement from
the zeta23 Challenge surface, choose the pins, and rerun Anthropic's own Lean
proof first, crediting Anthropic for that row.

## Reproduce

```sh
python3 code/verify.py
```

No network access and no Lean toolchain required; `mpmath` is used for the
transcendental cross-checks when present but is not required (the exact-rational
checks stand alone). Exit status 0 means all checks passed.

The Lean build itself is not reproduced here. Reproducing it needs the zeta23
checkout at `16a5ce41` plus a warm Mathlib cache; `BUILD.md` in the audited
package gives the exact commands.

## Scope

This audit covers the *correctness and internal consistency* of the audited
Lean package at its published commit. It does **not** establish that the
board route is open, does not create a Lean Verified row, does not re-run
Anthropic's own proof of the `2 - 1/cMT` row, and does not port the proof
library to the verifier's site pins.

## Credits

- **Anthropic** (`anthropics/formal-math`, `16a5ce41`) -- the `kappa* >= H`
  mathematics, the Challenge surface, Theorem D, and the `cMT` constant. Named
  first, per the board's route policy.
- **The audited package** -- the rational bridge `H >= 269/400`, the
  epsilon-adapter, and the identity linking the page form to `2 - 1/cMT`.
- **This audit** -- independent recomputation of the certificate, the
  orientation analysis, the receipt-authenticity check, and the pin-level
  reading of the Mathlib and zeta23 sources.
