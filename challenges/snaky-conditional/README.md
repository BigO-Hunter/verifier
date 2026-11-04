# SnakyConditional: trusted statement

Board: [Snaky](https://bigospeedrun.com/other/snaky), the family board. This folder proposes the
trusted statement for a new problem slug `snaky-conditional`
(https://bigospeedrun.com/other/snaky-conditional once enabled). It is not a proof of a move bound.

## Relation to `snaky`

The Snaky board tracks [`BigOSpeedrun.Snaky.Bound n`](../other-snaky/), a parameterization of
OpenAI's `SnakyTwentyOne.lean`. This folder freezes OpenAI's `SnakyConditional.lean`: the same
game and the same claim shape, fixed at `n = 35` (the SnakyTwentyOne statement with 21 replaced
by 35 and 20 by 34). The corpus tracks it as its own challenge — the sibling descriptor
`SnakyConditional.json` names the challenge module `ComparatorChallenges.SnakyConditional`, the
solution module `OAI.GameTheory.SnakyConditional.Main`, and the theorem
`OAI.SnakyConditional.snaky_winning_strategy_with_legal_states` — so it takes its own statement
folder here. No equivalence between the two namespaces is assumed; a submission proves `Bound n`
in `BigOSpeedrun.SnakyConditional` itself.

## Files

- `Statement.lean`: OpenAI's `lean/ComparatorChallenges/SnakyConditional.lean` at commit
  `1581d4cbdd69a0faf34b2089614fe2a814316a6a` of https://github.com/openai/math (Apache-2.0),
  copied byte for byte. The file's `sorry` is OpenAI's challenge placeholder — the claim to
  prove, not an assumed proof of any bound. See `provenance.json`.
- `Target.lean`: the target adapter, in a separate file so the frozen text stays untouched.
  `BigOSpeedrun.SnakyConditional.Bound n` is the corpus statement with `35` replaced by `n` and
  `34` by `n - 1`.
- `LICENSE`: Apache-2.0, the license of the source repository.
- `provenance.json`: source, commit, paths, hashes, authors, pins.

## What `Bound n` says

The board is the infinite square grid `ℤ × ℤ`. Maker moves first. Each Maker move claims one
cell, and each Breaker reply claims one cell. Maker wins when its cells contain the six-cell
Snaky `{(0,0), (1,0), (2,0), (3,0), (3,1), (4,1)}` in one of the eight orientations (rotations
and reflections), at any translation.

`Bound n` says: there is one Maker policy `σ` such that, against every legal Breaker sequence
`β`, after `n` Maker moves:

- Maker's cells contain a Snaky (`HasSnaky`);
- Maker has exactly `n` cells;
- no Maker cell is a Breaker cell (checked against Breaker's cells after `n - 1` replies), and
  Breaker has exactly `k` cells after `k` replies.

Details that a reviewer checks:

- The policy gets the number of moves left, Maker's cells and Breaker's cells. It must always
  give a fresh cell, on every state, also on states that play never reaches. On the infinite
  board this is no restriction.
- Breaker's sequence is chosen after `σ`, so it can answer every Maker move. A Breaker reply
  must be a fresh cell for every reply before Maker's last move (the corpus names this
  condition `LegalRepliesBeforeFinal`). Breaker's reply after Maker's last move is not
  restricted, and the result does not use it.
- Maker can win before move `n`. Its later moves are fresh cells, and the Snaky stays.
- No finite board, cost model or time limit is part of the target.

## The bound parameter

`n` is the number of Maker moves, a whole number (the form should refuse a fraction, as for
`snaky`). Smaller is better: `Bound n` gives `Bound m` for every `m ≥ n` (monotonicity, proven
for the sibling statement in [`challenges/other-snaky/Validation.lean`](../other-snaky/Validation.lean)),
so a smaller bound is stronger and a proof of a bound proves every larger bound. The frozen
statement is the instance `n = 35`. The claim is false for `n < 6` (the Snaky has six cells;
`not_bound_of_lt_six` in the sibling `Validation.lean`). Larger `n` is weaker.

## Pins

Lean `leanprover/lean4:v4.34.1` and the Mathlib pin of `profiles/lake-manifest.json`
(`d13f23b723b8a846827a245b89c10fc7d3f11612`), the same pin as `dft`, `catalan` and `other-snaky`.
Mathlib and its pinned dependencies only — no external libraries, build hooks, network
downloads, custom axioms, or compiled files.

## Provenance

- Source repository: https://github.com/openai/math
- Source commit: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`
- Original path: `lean/ComparatorChallenges/SnakyConditional.lean`
- Original git blob: `2a96224d351fbb48555ae55bd8f92589f8d2dc3e`
- File sha256: `3ab27d66779b557d0efcc3cfcf8317c40511e3cc655da29e61e95ba3f34d45ea`
- Statement region sha256 (lines 44-53, the theorem declaration through `:= by`):
  `8251a147ac18d65d2b71a45abffc8703dc7e324cd4f5e9e7047eee574b1313ad`
- Authors: OpenAI (repository owner; as recorded for the sibling statement). The introducing
  commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a` is authored by `Anonymous <anonymous@computer.local>`.
- License: Apache-2.0. `Statement.lean` is copied unchanged, so the source's license and
  attribution apply to it; `LICENSE` carries the license text.

## Pre-built proof

A kernel-checked proof of the frozen statement exists at
https://github.com/darkhipo/snaky-conditional (commit `96e0832b745f67ce354beedcda216b0aadffe045`):
zero `sorry`, axioms exactly `[propext, Classical.choice, Quot.sound]`, entry
`OAI.SnakyConditional.snaky_winning_strategy_with_legal_states`, statement region byte-exact
(sha256 `8251a147…`). It certifies `Bound 20`: the Snaky is secured by Maker claim 20 (the
verified Bound 20 win of issue #114, replayed through a padded policy) and moves 21-35 are
fresh filler, so the N = 35 instance is proved at a bound strictly better than 35.
