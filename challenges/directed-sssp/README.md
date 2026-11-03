# Directed shortest paths at every edge density: trusted statement

This is the trusted target for the
[directed shortest paths board](https://bigospeedrun.com/directed-sssp).
The issue route does not take this problem yet (`submissions.CLOSED`).

## Model

The computation model is the word RAM of the C-HD proof, from our fork
[bigospeedrun/c-hd-proof](https://github.com/bigospeedrun/c-hd-proof) of
spicylemonade/c-hd-proof, directory `formal/lean`, files `Frontier/Spec.lean`
and `Frontier/CostModel.lean`. The verifier clones the fork at the commit that
`profiles/direct.json` pins (`solution_dependencies`) and stages its `Frontier`
modules. This repository has no copy of them.

- A graph is an explicit list of `m` directed edges on `n` vertices, with
  nonnegative real weights. Parallel edges and self-loops are allowed.
- A program is a finite statement tree with a procedure table. Real values
  allow only 0, addition, loads and comparison. Words are bounded by
  `(n+m+2)^(wordExp+1)`; an overflow or an out-of-bounds access stops the run.
- Each statement and test costs 1, an allocation of `k` cells costs `k+1`, and
  a call costs 1. Runs are deterministic.
- `State.Solves` requires the exact distance of every vertex from the source
  (`⊤` when it is unreachable).

## Statement

A row says: "on graphs with at most D(n) edges, the time is O(T(n))", with

    D(n) = n^a · ⌊⌊log₂ n⌋^b⌋
    T(n) = n^a' · (ln n)^b' · (ln ln n)^c'

`BigOSpeedrun.DirectedSSSP.Bound a b a' b' c'` says that one program `P` and
constants `C > 0`, `N ≥ 16` exist such that:

1. on every graph with `n ≥ N` vertices and `m ≤ D(n)` edges, and every source,
   `P` stops with the exact distances at cost at most `C · T(n)`;
2. on every graph and every source, `P` stops with the exact distances at cost
   at most `C · (n+1) · (m+1)` (a polynomial fallback, as Bellman-Ford).

The edge cap is exact, with constant 1, because the C-HD program dispatches on
that exact cap. `N ≥ 16` makes `ln n ≥ 1` and `ln ln n ≥ 1`, so negative `b'`
and `c'` are well defined. `P.Exact` follows from clause 2; it stays in the
statement for readability.

The verifier writes the target from the five exponents:

```lean
theorem Race.bound : BigOSpeedrun.DirectedSSSP.Bound ((1 : ℚ) / 1) ((3 : ℚ) / 4) ((1 : ℚ) / 1) ((11 : ℚ) / 12) ((0 : ℚ) / 1) := by
  sorry
```

## Bound field

The issue form takes the bound as `D ; T` in one normal form, for example
`n log^3/4 ; n log^11/12`:

- `D` is `n^a log^b` and `T` is `n^a' log^b' loglog^c'`, with the factors in this
  order and one space between them;
- each exponent is an integer or a reduced fraction (`3/4`, `-1/2`), with at
  most 40 digits per integer;
- a factor with exponent 0 is left out, and exponent 1 is the bare name (`n`,
  not `n^1`);
- `1 ≤ a ≤ 2`, `b ≥ 0`, and `D` is at most `n^2`;
- `T` is at least `D` and at most `n^3`.

`submissions.parse_sssp` refuses every other text with a message that shows the
example.

## Comparison

For these functions, `f = O(g)` exactly when the exponent tuple of `f` is at
most that of `g` in lexicographic order. The verifier and the site compare the
rational tuples `(a, b)` for `D` and `(a', b', c')` for `T`; they use no reals.

A row is a record when its `T` is strictly below the best `T` among the listed
rows whose `D` is at least as dense. `Validation.lean` proves the two facts
that this rule uses:

- `weaker_time`: a row also proves every slower time at the same density;
- `cover_sparser`: with `b₀, b ≥ 0`, a row also proves its time at every sparser
  density.

It also proves `cap_ge_self` (for `a ≥ 1`, `b ≥ 0` and `n ≥ 2`, the cap is at
least `n`, so clause 1 is not empty) and `time_pos`.

## Pins and builds

Lean `leanprover/lean4:v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and the other revisions in
`profiles/lake-manifest.json`. The fork itself pins Lean v4.34.0 and Mathlib
`5ed2965`; its `formal/lean` tree builds unchanged on our pins. That tree sets no
Lean options, so its own build keeps Lean's default `autoImplicit = true`, and
`Frontier/CHD/MergeSort.lean` uses an auto-bound name. The profile gives only the
`Frontier` root that option (`lean_options` of the solution dependency); the
submission, the challenge and the audit keep `autoImplicit = false`. The option
acts only where a name is otherwise unknown, so `Frontier.Spec` and
`Frontier.CostModel` mean the same under either setting.

The statement and `Validation.lean` were built on GitHub Actions in
[bigospeedrun/sssp-lean-scratch](https://github.com/bigospeedrun/sssp-lean-scratch)
(runs 41609770176 and 41609775031, on our pins and on the fork's pins, with the
full C-HD proof). `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound`. Builds that import the C-HD model run on GitHub Actions only.
