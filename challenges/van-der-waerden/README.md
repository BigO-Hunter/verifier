# QuantitativeVanDerWaerden: trusted statement

Board: [Van der Waerden](https://bigospeedrun.com/other/van-der-waerden). This folder proposes the
trusted statement for the problem slug `van-der-waerden`
(https://bigospeedrun.com/other/van-der-waerden once enabled). It is not a proof of a bound.

## Relation to the corpus

This folder freezes OpenAI's `QuantitativeVanDerWaerden.lean`: the van der Waerden number
`W r k` and the uniform quantitative lower bound on it. The corpus tracks the same claim as its
own challenge — the sibling descriptor `QuantitativeVanDerWaerden.json` names the challenge
module `ComparatorChallenges.QuantitativeVanDerWaerden`, the solution module
`OAI.Combinatorics.ProgressionColoring.Main`, and the theorem
`OAI.QuantitativeVanDerWaerden.uniform_lower_bound` — so it takes its own statement folder here.
A submission proves `Bound c` in `BigOSpeedrun.VanDerWaerden` itself.

## Files

- `Statement.lean`: OpenAI's `lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean` at
  commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a` of https://github.com/openai/math
  (Apache-2.0), copied byte for byte. The file's `sorry` is OpenAI's challenge placeholder — the
  claim to prove, not an assumed proof of any bound. See `provenance.json`.
- `Target.lean`: the target adapter, in a separate file so the frozen text stays untouched.
  `BigOSpeedrun.VanDerWaerden.Bound c` is the corpus statement with the constant `1/100000`
  replaced by a free rational `c`.
- `LICENSE`: Apache-2.0, the license of the source repository.
- `provenance.json`: source, commit, paths, hashes, authors, pins.

## The model and what `Bound c` says

`W r k` is the van der Waerden number: the least positive `N` such that every `r`-coloring
`c : ℕ → Fin r` of the naturals has a monochromatic arithmetic progression of length `k`
entirely below `N` (`IsRamsey (Fin r) k N` in `Statement.lean`; `MonoAP c k a d` is the
monochromatic progression `a, a+d, …, a+(k-1)d`). The model is pure combinatorics — no RAM, no
cost model, no time limit is part of the target. Uniformity is over all color counts `r ≥ 2`.

`Bound c` says: there is a threshold `K` such that for every `k ≥ K` and every `r ≥ 2`,

    k ^ (c · k · ⌊log₂ r⌋)  <  W r k.

This is a **lower** bound on the van der Waerden number: it asserts `W r k` is large. The
conclusion is the scored step itself (a quantified lower bound on `W`), not arithmetic of a
single example.

## The bound parameter

`c` is the exponent constant, a rational `p/q` with `q > 0`. **Larger `c` is better**: it gives a
stronger lower bound on `W r k` (a larger `c` makes `k^(c·k·⌊log₂ r⌋)` bigger, so `W` is pushed
higher). The bound is **attained**: the form takes one specific rational, and a proof of `Bound c`
proves `Bound c'` for every `c' ≤ c` (a smaller exponent is a weaker, easier inequality). The
frozen corpus statement is the instance `c = 1/100000`.

Range: the method's strict frontier is `c = 1/8`, which is **not an attained value** — every
fixed `c < 1/8` is admitted, `1/8` itself is not (board semantics: strict frontier; a strict
frontier needs a separate contract change, so submissions file an attained `c < 1/8`). The
baseline row is `c = 1/100000`.

## Pins

Lean `leanprover/lean4:v4.34.1` and the Mathlib pin of `profiles/lake-manifest.json`
(`d13f23b723b8a846827a245b89c10fc7d3f11612`), the same pin as `dft`, `catalan` and `other-snaky`.
Mathlib and its pinned dependencies only — no external libraries, build hooks, network
downloads, custom axioms, or compiled files. Permitted proof axioms are exactly `propext`,
`Classical.choice`, `Quot.sound`.

## Controls (reviewer questions, issue #140)

The statement is **unconditional** — `∃ K, ∀ k ≥ K, ∀ r ≥ 2` — so it fixes no hypotheses and a
submission cannot add any (issue #140 Q2: a hypothesis may appear only when the trusted statement
fixes it). On the three review questions:

- **Q1 — direction / scored step.** The conclusion is the quantified lower bound on `W r k`
  itself (`k^(c·k·⌊log₂ r⌋) < W r k` for all large `k`, all `r ≥ 2`), not the value of one
  instance. This is the scored step. A `decide`-shaped finite count would not be a proof of the
  row; this statement asserts the full claim.

- **Q2 — hypotheses.** None. The claim is unconditional (the only bound is the quantifier
  `k ≥ K`, `r ≥ 2`, which is the claim's own scope, not an assumption). There is no hypothesis
  set to fix or to inflate. This is why the route is an assembly, not a formalization project.

- **Q3 — vacuity / boundary controls.**
  - *Joint satisfiability.* Vacuous here — there are no hypotheses to satisfy — but the claim is
    genuinely non-vacuous: `W r k` is finite and positive for `r ≥ 2`, `k ≥ 1` (finite van der
    Waerden numbers exist by Ramsey theory, so the `sInf` defining `W` is over a non-empty set),
    and the `∃ K` is inhabited. The statement is therefore neither empty nor trivially true.
  - *Below-minimum control.* The bound is one-sided and monotone: `Bound c` implies `Bound c'`
    for `c' ≤ c`, so a weaker constant is always obtainable and never breaks the row. The
    genuinely unprovable direction is a constant the construction does **not** yield: a `c` above
    the construction's yield (and in particular any `c ≥ 1/8`) is not provable from this method,
    because `W r k` is not known to exceed `k^(c·k·⌊log₂ r⌋)` there. A submission below the true
    yield is trivially extendable (monotonicity); a submission above it is refuted by the method's
    ceiling. The reviewed row carries an attained `c` strictly above the `1/100000` baseline so
    the run is not a tie.

## Provenance

- Source repository: https://github.com/openai/math
- Source commit: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`
- Original path: `lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean`
- Original git blob: `bee3f5a820455ead2a00f8fdc08d4ae5276cba2a`
- File sha256: `1caa563bbf7a5602adb8cdbbc06aaf1e3d4d5fe27ed4bebf2bf44cf2937a6593`
- Descriptor: `lean/ComparatorChallenges/QuantitativeVanDerWaerden.json`, git blob
  `10b1770000baae70cfe28b4890143ff9960273af`.
- Authors: OpenAI (repository owner). The introducing commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`
  is authored by `Anonymous <anonymous@computer.local>`.
- License: Apache-2.0. `Statement.lean` is copied unchanged, so the source's license and
  attribution apply to it; `LICENSE` carries the license text.

## Pre-built proof — assembly with credit

The proof is an **assembly of the cataloged, sorry-free corpus solution**, not new mathematics.
The complete solution tree `lean/OAI/Combinatorics/ProgressionColoring/` (117 files at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, cataloged complete in `lean/formalization.yaml`)
closes with `exact uniform_lower_of_cyclicLowerBound exists_cyclic_coloring`
(`Main.lean`, git blob `d8ca9d7ce4f064bf9573aefb9e1e136063d2d991`).

**Credit.** The van der Waerden lower bound and its entire formalization — the cyclic-coloring
construction, the mesh/counting machinery, and the closing `uniform_lower_bound` theorem — are
the work of the **openai/math authors (OpenAI)**. This package only freezes the statement,
parameterizes the constant, and packages the assembled proof for the verifier. Every mathematical
step is theirs; per the community's attribution norm (issue #142), that credit is stated here
with receipts (repository, commit, file paths, git blobs above).

## Row note (margin)

The baseline row is `c = 1/100000`. Landing exactly at `1/100000` **ties** the baseline, and a
tie starts no run — so a filed row must carry an attained `c` strictly greater than `1/100000`.
The corpus constant `1/100000` is a conservative value (`Parameters.c`); the construction admits
a larger `c`. The transfer `uniform_lower_of_cyclicLowerBound` is `c`-generic, and the constant is
set by the construction budget: the rich-risk coefficient `(1/100)/80 − 2·c`, hardcoded as
`21/200000` at `c = 1/100000`. Re-tuning the `c` literals and that coefficient (a parameter
re-tune, not new math) reaches larger attained `c`; the coefficient stays positive for
`c < 1/16000`, so attained `c` up to just below `1/16000` is the ceiling of this construction.
`c = 1/20000` is verified by the assembled proof (5× the baseline; see the proof README).
**`c > 1/9` (the leading Claimed value) is NOT reachable from this construction** — the ceiling
`1/16000` is far below `1/9` — so the row is a verified improvement of the baseline and the first
Lean Verified row for the board, not a rank-1 challenge to the (unverified) Claimed values.
