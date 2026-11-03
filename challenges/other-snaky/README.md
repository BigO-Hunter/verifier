# Snaky Maker-move bound: trusted statement

Board: https://bigospeedrun.com/other/snaky

`VerifierStatement.lean` is the trusted statement of the `snaky` profile (issue route, opened
2026-11-03). It is not a proof of a move bound.

For a whole number `n`, the race target is:

```lean
theorem Race.bound : BigOSpeedrun.Snaky.Bound n := by
  -- proof supplied by a contributor
```

A smaller `n` is better. The verifier supplies the statement and puts the submitted number in
place of `n`. The contributor does not choose the board, the shape or the rules.

## Files

- `Model.lean`: OpenAI's definition block from `lean/ComparatorChallenges/SnakyTwentyOne.lean`
  at commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a` of https://github.com/openai/math
  (Apache-2.0). Lines 3-40 of the original file are copied byte for byte (lines 9-46 here). The
  changes: an attribution header, four narrower Mathlib imports in place of `import Mathlib`, no
  unproved 21-move theorem, and `end OAI`. See `provenance.json`.
- `Statement.lean`: `BigOSpeedrun.Snaky.Bound n`, by fluorine with OpenAI Codex (verifier PR #65).
  It is OpenAI's 21-move statement with `21` replaced by `n` and `20` by `n - 1`.
- `VerifierStatement.lean`: `Model.lean` followed by `Statement.lean` without its import line.
  This is the one self-contained file that the verifier copies into a submission. Its only
  imports are Mathlib modules. A submission imports it and must not change it.
- `Validation.lean`: checks of the statement (below). It is not part of the trusted target.

## What `Bound n` says

The board is the infinite square grid `ℤ × ℤ`. Maker moves first. Each Maker move claims one
cell, and each Breaker reply claims one cell. Maker wins when its cells contain the six-cell
Snaky `{(0,0), (1,0), (2,0), (3,0), (3,1), (4,1)}` in one of the eight orientations
(rotations and reflections), at any translation.

`Bound n` says: there is one Maker policy `σ` such that, against every legal Breaker sequence
`β`, after `n` Maker moves:

- Maker's cells contain a Snaky (`HasSnaky`);
- Maker has exactly `n` cells;
- no Maker cell is a Breaker cell, and Breaker has exactly `k` cells after `k` replies.

Details that a reviewer checks:

- The policy gets the number of moves left, Maker's cells and Breaker's cells. It must always
  give a fresh cell, on every state, also on states that play never reaches. On the infinite
  board this is no restriction: `freshPolicy_fresh` gives such a policy.
- Breaker's sequence is chosen after `σ`, so it can answer every Maker move. A Breaker reply
  must be a fresh cell for every reply before Maker's last move. Breaker's reply after
  Maker's last move is not restricted, and the result does not use it: the disjointness
  check uses Breaker's cells after `n - 1` replies.
- Maker can win before move `n`. Its later moves are fresh cells, and the Snaky stays.
- No finite board, cost model or time limit is part of the target.

## Validation

`Validation.lean` uses only the axioms `propext`, `Classical.choice` and `Quot.sound`:

- `card_snaky`, `six_le_card_of_hasSnaky`: every placed Snaky has six cells.
- `freshPolicy_fresh`: a policy can meet the freshness condition.
- `card_maker_of_fresh`: freshness forces `card = n`, so that conjunct excludes no winning policy.
- `reply_legal`: against every policy, a legal Breaker exists. So the Breaker hypothesis is
  never empty, and `Bound n` cannot hold without a real Maker win.
- `not_bound_of_lt_six`, `not_bound_zero`: `Bound n` is false for `n < 6`.
- `bound_succ`, `bound_mono`: `Bound n` gives `Bound m` for every `m ≥ n`. So a smaller bound
  is stronger, and a proof of a bound proves every larger bound.
- `bound_twentyOne_iff`: `Bound 21` is OpenAI's 21-move statement, by `Iff.rfl`.

To run them, put `VerifierStatement.lean` and `Validation.lean` in a Lake project with the
profile manifest and `lean-toolchain`, and run `lake build VerifierStatement Validation`.

## Pins

Lean `leanprover/lean4:v4.34.1` and the Mathlib pin of `profiles/lake-manifest.json`
(`d13f23b723b8a846827a245b89c10fc7d3f11612`), the same pin as `dft` and `catalan`.

## Other representations

The independent 19-move audit concerns `Snaky.PlaneBlackWinsIn`, a different representation.
No equivalence between the two is assumed. A submission proves `Bound n` itself.
