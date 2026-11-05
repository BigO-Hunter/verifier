# Zeta zeros on the critical line: Anthropic's theorem D, cumulative form

This is the statement of the [Zeta zeros on the critical line board](https://bigospeedrun.com/other/critical-line-zeros)
for Anthropic's row. `Challenge.lean` is `zeta23/Challenge.lean` from
[anthropics/formal-math](https://github.com/anthropics/formal-math) commit
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, byte for byte. Its only import is Mathlib: the
definitions of `ChallengeDeps.lean` are inlined in it. `LICENSE` and `NOTICE` are their files, unchanged.

The file states 17 theorems with `sorry`. Only one is a target here, the board quantity:

```lean
theorem montgomery_taylor_simple_on_critical_line_mult_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
```

`Ncount 0 T` counts the nontrivial zeros of Mathlib's `riemannZeta` with `0 < Im ρ ≤ T`, with
multiplicity (`analyticOrderAt`). `N0simple 0 T` counts those with `Re ρ = 1/2` and multiplicity 1.
So the theorem says `liminf N₀ˢ(T)/N(T) ≥ 2 − 1/cMT`, which is `κ* ≥ 2 − 1/cMT` on the board. With
`ϑ = 1/√2`, `cMT = √2·tan ϑ / (1 + ϑ·tan ϑ)`, so `1/cMT = 1/2 + cot ϑ/√2` and

    2 − 1/cMT = 3/2 − cot(1/√2)/√2 = H ≈ 0.6725007036794,

the Montgomery–Taylor constant of the board. The other 16 theorems (dyadic windows, the
constants 2/3 and 5/6, distinct zeros, Dirichlet L-functions) keep their `sorry` here and are
not targets.

## Run

This profile is closed to issues and PRs. Only a maintainer can run it, with the
`Verify a Lean proof` workflow on GitHub Actions:

- `repo_url`: `https://github.com/anthropics/formal-math`
- `commit`: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`
- `challenge_file`: `challenges/critical-line-zeros/Challenge.lean`
- `theorem_names`: `montgomery_taylor_simple_on_critical_line_mult_cumulative`
- `lean_toolchain`: `leanprover/lean4:v4.33.0-rc2`

The run builds the import closure of their `Solution` from the folder `zeta23` (roots `Solution`,
`ChallengeDeps` and `Zeta23`). It does not use their Lake files, scripts or compiled objects, and
their own `Challenge.lean` is not staged. Comparator checks the elaborated statement of their
`Solution` against this file, and the axiom audit admits only `propext`, `Quot.sound` and
`Classical.choice`.

Lean `v4.33.0-rc2` and Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` are their pins:
[profiles/zeta23-lake-manifest.json](../../profiles/zeta23-lake-manifest.json) is their
`lake-manifest.json`, unchanged. The tools are in
[profiles/tools-v4.33.0-rc2.json](../../profiles/tools-v4.33.0-rc2.json): Comparator `7892797` and
lean4export `9fb131bb` (its `v4.33.0-rc2` tag); landrun, nanoda and elan as in our other tool files.
Comparator `7892797` is the merge of its pull request #65 (the fix of issue #64), the last Comparator
commit on Lean `v4.33.0-rc2`, and its own manifest pins lean4export `9fb131bb`. Their CI (run
33213372463, 2026-08-28) used Comparator `57567492`, built with that commit's own toolchain
`v4.34.0-rc1`. Our setup builds Comparator with the toolchain of the profile, and `57567492` does
not build with `v4.33.0-rc2`. The Comparator changes after `7892797` add multi-kernel support and
fix issues #67 and #71; #71 applies only to a target named `Quot.mk`, `Quot.lift` or `Quot.ind`.
Issue #68 (a constant reached only through `Expr.proj` is not compared) is fixed in Lean core
(leanprover/lean4#14728), not in `v4.33.0-rc2`. It does not apply here: `Challenge.lean` declares no
structure, and every structure it reaches comes from the pinned Mathlib build, which `Solution` cannot
redefine.

Their lakefile sets `relaxedAutoImplicit = false` and `pp.unicode.fun = true` and leaves
`autoImplicit` at Lean's default, `true`. The profile keeps `autoImplicit = true` (`auto_implicit`).
The two other options are not set: `relaxedAutoImplicit = false` only refuses sources that it
changes, and `pp.unicode.fun` only changes printing.
