# Audit — Catalan's constant irrationality measure, independent local build + exact recomputation

Row: **catalan** — **μ(G) ≤ 295** [Claimed], S. Litsey (slitsey),
[github.com/slitsey/catalan-irrationality-measure](https://github.com/slitsey/catalan-irrationality-measure)
@ `65cfcc216b2fd8a6c52f84a8ea41fb654b11eddb` (2026-11-06). Claim shape: `|G − a/b| > b^(−295)`
for every integer `a` and all sufficiently large `b`, where `G = ∑ (−1)^j/(2j+1)²`.

The claim is a **Lean 4 formalization**: the theorem
`CatalanIrrationalityMeasure.catalan_irrationalityMeasure_295` (`Challenge.lean` = statement surface
with the one placeholder `sorry`; `Solution.lean` = proof), resting on a 58×N-determinant construction
of OpenAI's irrationality proof at design (58, 9, 3, 5, 3), a corank (denominator) ledger, a
Pick-matrix/Blaschke row-determinant bound, Davis quadrature nodes, and a criterion whose final
numeric condition is `295(η − 4dδ) > dρ` with d = 53, ρ = 295.849794, η = 53.16065, δ = 2.9·10⁻⁷.

**VERDICT: VERIFIED-WITH-CONDITIONS — the formalization builds cleanly at its pinned toolchain
and the top theorem is axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no
unlisted axioms); every numeric step of the criterion chain was independently recomputed in exact
rational arithmetic and matches to the last digit; the conditions are (i) toolchain v4.35.0-rc2 vs
the board verifier's v4.34.1 pin, so the board cannot currently re-verify without a toolchain bump
(author informed via issue #8), (ii) `lake comparator` has not been run for the 295 route
(author-disclosed; kernel recheck via `lake build` is the load-bearing verification and it passes).**

Independence: slitsey is not the auditor. The auditor's lines on this board are
darkhipo/catalan-constant-gen5 (μ ≤ 528.2315) and the 410-era chain — superseded by this row. This
audit disputes nothing of ours; it is a community-lane audit per #97/#102/#124/#138 precedent.

## Checklist

| # | Item | Verdict | Evidence |
|---|---|---|---|
| 1 | Artifact pin | **PASS** | clone of `slitsey/catalan-irrationality-measure` @ `65cfcc21`; `lean-toolchain` = `leanprover/lean4:v4.35.0-rc2`; Mathlib pinned `065356127b1d` (v4.35.0-rc2) in `lake-manifest.json` (`evidence/pin.txt`). |
| 2 | Build at pinned toolchain | **PASS** | full `lake exe cache get` + `lake build Solution` on the pinned rc-2 toolchain: **zero errors** across all modules (vendored OAI/ + PrimeNumberTheoremAnd/ + CatalanMeasure/ + Solution); certificate-heavy modules kernel-check in seconds-to-minutes each (`evidence/build_tail.log`). |
| 3 | Axiom audit of the top theorem | **PASS** | `#print axioms catalan_irrationalityMeasure_295` → `[propext, Classical.choice, Quot.sound]` — the three standard axioms, exactly as the README claims. No `sorryAx`, no `native_decide`, no unlisted axioms (`evidence/axioms.txt`). |
| 4 | Statement ↔ board row | **PASS** | `Challenge.lean` states exactly `∀ᶠ b in atTop, ∀ a : ℤ, b^(−295) < |G − a/b|` with G as the literal alternating series — the board's μ(G) ≤ 295, no weaker reading. |
| 5 | Criterion chain, exact arithmetic | **PASS** | all Lean literals recomputed with `fractions.Fraction` (220-digit decimal check): ρ = 147924897/500000 = 295.849794, η = 1063213/20000 = 53.16065, δ = 29/10⁸ — all match README/paper. Headline: `295·(η − 4·53·δ) − 53·ρ = 11672657/5000000 = 2.334531 > 0`, quotient 294.9560852980… < 295 (README "294.956…", paper `\Bstar` 294.95608 — consistent truncation) (`evidence/recompute_output.txt`). |
| 6 | Paper's seven criterion conditions | **PASS** | ρλ = 295 exact; η < 106; ω = 3/5 < λ; δ < 1/3; (λ−ω)(η+106(1−3δ)) = 63.207053 > 53; 2(ω−δ(2λ−ω)) = 1.1999992 > 1; d + 4dδλ = 53.0000613 < ηλ = 53.0079522 (slack 0.00789) (`evidence/criterion_conditions.txt`). |
| 7 | hgain step (`eta295_lt_of_gain`) | **PASS** | η = 53.16065 < 58²·(T296 − log 2/2) − gDg(22.0607) = 53.16166490, slack ≈ 0.00101 at 220 digits. The gain constant 220607/10000 = 22.0607 is the corank-ledger area; the ledger theorem `LedgerContent.content` is in the build and axiom-clean per its own `#print axioms` in the build log. |
| 8 | Failure-class scan (hardcoded residuals) | **PASS** | repo architecture makes literals the *inputs*: every claimed inequality is re-checked by the kernel (`decide +kernel`; README states Arb/float generators are untrusted). Grep of the whole proof path: **zero** tactic-position `native_decide`, **zero** tactic-position `sorry` outside the Challenge statement placeholders (1 in `Challenge.lean`, 16 in `ChallengeHybrid.lean` — the statement surface), **zero** `axiom`/`opaque` declarations (`evidence/static_checks.txt`). Docstrings in `AngPilot/AngAux` that *mention* "sorry/native_decide" are negative claims, verified true by the kernel. |
| 9 | Reproducibility / receipt | **PASS** | the certificate receipt IS the build: recompiling `Solution.lean` re-runs the Lean kernel over every certificate declaration (exact ℚ comparisons, modular inverses mod 1009, Chebyshev/Clenshaw recurrences by 2-power quotients). Reproduced here end-to-end from the pinned toolchain. |
| 10 | Scope honesty (row conditions) | **DISCLOSED** | author discloses: comparator not run for 295 (`comparator.json` present; needs Linux+bwrap); toolchain rc-2 vs board verifier v4.34.1 (issue #8); proof built on OpenAI's formalization (489 vendored files ported to the module system, `NOTICE`/`PORTING.md`) and 33 Davis files (commit `3c45153`, Apache-2.0); authorship is AI-produced under human direction (stated in README + `formalization.yaml`). |

## Discrepancies — none invalidate the row

- **D1 — toolchain (the real board condition):** the pinned toolchain is a *release candidate*
  (v4.35.0-rc2) and the development requires Lean's new module system; the board's Catalan verifier
  pins v4.34.1 and cannot build it (BOS's own outreach, issue #8, asks the same about the 410 row).
  The mathematics is kernel-checked at rc-2; **Lean Verified status on the board requires either a
  verifier toolchain bump or a back-port.** The records page should annotate this.
- **D2 — comparator gap (disclosed):** `lake comparator` (NanoDa/con-ron external kernels) has not
  run on the 295 route. Belt-and-braces only — the standard kernel check passes — but the README's
  own "kernel-checked" claim for 295 rests on `lake build` alone. Suggest the author run it in CI
  (Linux runner) or the verifier note it.
- **D3 — internal-route naming:** the chain is assembled at internal `B = 296` constants
  (`Theorem296`, `rho296`, `psi296`) with the 295 claim discharged through
  `Count.WinCertGlue.eta295_lt_of_gain` (gain ≥ 22.0607). Verified consistent end-to-end; flagged
  only because a future reader grepping for "296" may be confused.
- **D4 — 727.03 (issue #5):** ry-xu's κ=2 improvement claim on the ledger is *not* formalized and is
  correctly described as such in the README ("numerical certificate in ball arithmetic that is not
  formalized"). No action.

## Honest limits

This audit certifies the **formalization**, not the underlying mathematics independently: the Lean
kernel is trusted (as in every Mathlib-based board row), and the ported OpenAI formalization + Davis
files are used as deposited (Apache-2.0, provenance documented; the 37 point-evaluation files with
7-digit comparison constants are stated to be outside the import closure of these theorems — checked
by import closure of the build, not line-by-line). A defect in OpenAI's original argument that is
faithfully formalized would produce a faithfully formalized wrong theorem; no independent
re-derivation of the determinant/energy mathematics was attempted. What WAS independently
re-derived: the full numeric criterion chain (checklist 5–7), the statement↔row identity, and the
axiom surface (checklist 3).

## This PR

**Title:** `Audit: local build + exact recomputation of the catalan μ(G) ≤ 295 row (slitsey @ 65cfcc21)`

## File guide

| Path | Contents |
|---|---|
| `NOTICE.md` | attribution, independence statement, honest limits |
| `RESULT.json` | machine-readable verdict, pins, key numbers |
| `MANIFEST.json` | sha256 of every file in this package |
| `verify.py` | exact-arithmetic recomputation of the criterion chain (stdlib only) |
| `evidence/pin.txt` | audited commit |
| `evidence/recompute_output.txt` | criterion chain recomputation (exact) |
| `evidence/criterion_conditions.txt` | the paper's seven conditions, exact |
| `evidence/static_checks.txt` | sorry / native_decide / axiom greps (all empty) |
| `evidence/axioms.txt` | `#print axioms` outputs for the top theorem and the count ledger |
| `evidence/build_tail.log` | build log tail + error count |
