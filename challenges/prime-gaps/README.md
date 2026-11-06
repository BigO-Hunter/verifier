# Bounded gaps between primes: trusted statement

Board: https://bigospeedrun.com/other/prime-gaps

`Statement.lean` is the trusted statement of the `prime-gaps` profile. It is not a proof of a gap
bound. The profile is closed: the issue form does not offer it until a maintainer smoke run passes.

For a whole number `B`, the race target is:

```lean
theorem Race.bound : BigOSpeedrun.PrimeGaps.Bound B := by
  -- proof supplied by a contributor
```

`Bound B` is

```lean
∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ B
```

Here `Nat.nth Nat.Prime m` is the `m`-th prime, counted from `Nat.nth Nat.Prime 0 = 2`. So
`Bound B` says: infinitely often, two consecutive primes differ by at most `B`. That is
`H₁ ≤ B`, with `H₁ = liminf (p(n+1) - p(n))`, the quantity of the board. A smaller `B` is better.
`Bound 2` is the twin prime conjecture. The verifier supplies the statement and puts the submitted
number in place of `B`.

## Source

The proposition is the conclusion of Axiom Math's
`bombieriVinogradov_implies_frequently_prime_gap_le_246` in `PrimeGaps/Bounded246.lean` of
https://github.com/AxiomMath/PrimeGapsLib at commit `1faa7b14e82ddebc2772dfb9153922f01b106477`
(Apache-2.0), with `246` replaced by `B` and without its Bombieri-Vinogradov hypothesis. See
`provenance.json` and `NOTICE`.

## Review points

- The subtraction is on natural numbers. It hides nothing: `Nat.nth Nat.Prime` is strictly
  increasing (there are infinitely many primes), so each difference is the true gap.
- `∃ᶠ m in Filter.atTop` is "for infinitely many `m`". A finite list of small gaps (for example
  `3 - 2 = 1`) does not give a bound.
- The statement imports only Mathlib (three narrow modules) and defines one proposition.

## Validation

`Validation.lean` is not part of the trusted target. It builds with Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` (built 2026-11-06 on Nil's desktop; only `propext`,
`Classical.choice` and `Quot.sound`):

- `bound_mono`: `Bound B` gives `Bound B'` for `B ≤ B'`.
- `two_le_gap`, `not_bound_one`, `not_bound_lt_two`: after `2, 3` every gap is at least `2`, so
  `Bound 0` and `Bound 1` are false and `Bound 2` is the twin prime conjecture.
- `bound_iff_primes`: `Bound B` holds exactly when for every `n₀` there are primes
  `n₀ ≤ p < q ≤ p + B`, the form of Axiom Math's `bombieriVinogradov_implies_prime_gap_le_246`.

## Pins

Lean `leanprover/lean4:v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
(`profiles/anthropic-lake-manifest.json`).
