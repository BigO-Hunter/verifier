# Van der Waerden numbers: OpenAI's uniform lower bound at c = 1/100000

This is the statement of the [Van der Waerden numbers board](https://bigospeedrun.com/other/van-der-waerden)
for OpenAI's row. `Challenge.lean` is `lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean` from
[openai/math](https://github.com/openai/math) commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, byte for
byte. Its only import is Mathlib. `LICENSE` is their file, unchanged (Apache-2.0); the repository has no
NOTICE file.

The file defines `MonoAP`, `HasMonoAP`, `IsRamsey` and `W r k`, the least positive `N` such that every
coloring of `ℕ` with `r` colors has a monochromatic `k`-term progression below `N`. Its one theorem is the
target:

```lean
theorem uniform_lower_bound :
    ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by
```

`Nat.log 2 r` is `⌊log₂ r⌋`, so the theorem says `W_r(k) > k^{c k ⌊log₂ r⌋}` for all large `k`, uniformly
in `r ≥ 2`, with `c = 1/100000`: the board quantity at OpenAI's value.

## Run

This profile is closed to issues and PRs. Only a maintainer can run it, with the `Verify a Lean proof`
workflow on GitHub Actions:

- `repo_url`: `https://github.com/openai/math`
- `commit`: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`
- `challenge_file`: `challenges/van-der-waerden/Challenge.lean`
- `theorem_names`: `OAI.QuantitativeVanDerWaerden.uniform_lower_bound`
- `lean_toolchain`: `leanprover/lean4:v4.34.1`

The run fetches only `lean/OAI/Combinatorics/ProgressionColoring/` (sparse checkout) and stages that folder:
115 modules, whose imports reach only Mathlib. The solution module is
`OAI.Combinatorics.ProgressionColoring.Main`, as in their Comparator configuration
`lean/ComparatorChallenges/QuantitativeVanDerWaerden.json` (same theorem, same three axioms). The run does
not use their Lake files, patches or scripts, and their own copy of the challenge is not staged. Comparator
checks the elaborated statement of their solution against this file, and the axiom audit admits only
`propext`, `Quot.sound` and `Classical.choice`.

The pins are our defaults, which are also theirs at this commit: Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` ([profiles/lake-manifest.json](../../profiles/lake-manifest.json))
and the tools of [profiles/tools.json](../../profiles/tools.json). Their lakefile sets `autoImplicit = false`,
our default. Their other packages (and their compatibility patches) are outside the import closure of the
solution, so the run needs none of them.

Comparator issue #68 (a constant reached only through `Expr.proj` is not compared) does not apply: its fix
in Lean core (leanprover/lean4#14728, merged 2026-08-10) is in `v4.34.1`, and `Challenge.lean` declares no
structure.
