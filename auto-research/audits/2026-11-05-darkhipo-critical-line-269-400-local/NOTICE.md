# NOTICE -- provenance, attribution, and limits

## Audited package

- **`darkhipo/critical-line-269-400`** at commit `ac06cb570f`
  (`https://github.com/darkhipo/critical-line-269-400`), Apache-2.0.
  Files audited: `lean/HGe269.lean`, `lean/Bridge269.lean`, `lean/P2Plugs.lean`,
  `lean/adapter/RaceBound.lean`, `README.md`, `NOTICE.md`, `BUILD.md`,
  `docs/NUMBERS.md`, `docs/CERT.md`, `receipts/shasums.txt`,
  `receipts/build-final.log`.

## Upstream mathematics (credited first, per the board's route policy)

- **Anthropic** -- `anthropics/formal-math` at `16a5ce41` (zeta23 subtree last
  touched `2bafb8c8`), Apache-2.0. Consumed: the Challenge surface
  (`ChallengeDeps`: `Ncount`, `N0simple`, `cMT`), Theorem D cumulative
  (`Solution.montgomery_taylor_simple_on_critical_line_mult_cumulative`,
  `Zeta23.ThmD.thmD0_simple_mult_cumulative`), `Zeta23.ThmD.HD_one`, and
  `Solution.cStar_one_eq_cMT`. The `kappa* >= H` mathematics is Anthropic's.
- **Mathlib** at `51e6992efd06126df61a496bebf8f49482a4e129`, Apache-2.0.
  Consumed by the audited package: `Real.hasSum_sin`, `Real.hasSum_cos`,
  `Antitone.alternating_series_le_tendsto`, `Antitone.tendsto_le_alternating_series`
  (`Mathlib/Analysis/SpecificLimits/Normed.lean`), `Real.tan_eq_sin_div_cos`,
  `Real.cot_eq_cos_div_sin`, `Real.sq_sqrt`.

## This audit

Authored by the MultiAgency swarm (darkhipo agents), 2026-11-05. Read-only
analysis plus an exact-rational recomputation in `code/verify.py`. No Lean
build was run; no audited source file was modified.

## Honest limits

- The audited Lean build was **not** re-run. The receipt was checked for
  authenticity by re-locating its per-line axiom entries in the published
  sources, not by reproducing the build.
- The **proof-library port to the verifier site pins** (Lean `v4.34.1` +
  Mathlib `d13f23b7`) is **unmeasured** -- inherited from the audited package,
  which states the same limit. The package builds at zeta23's native pins
  (Lean `v4.33.0-rc2` + Mathlib `51e6992e`).
- The audit does not re-prove Anthropic's `2 - 1/cMT` row; it verifies that the
  audited package's identity bridge re-derives the identity zeta23 already
  establishes (`HD_one` + `cStar_one_eq_cMT`).
- The board route is **cold** (measured). This audit creates no Lean Verified
  row and asserts no board effect.

## AI-assistance disclosure

AI-authored (MultiAgency swarm), disclosed. The verification steps are
mechanical and reproducible via `code/verify.py`.
