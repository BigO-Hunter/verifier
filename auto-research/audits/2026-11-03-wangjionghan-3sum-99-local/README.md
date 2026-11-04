# Independent local Lean replay: 3SUM exponent 384055881637/200000000000 (issue #99)

## Claim and scope

The pinned submission `Wang-jiong-han/3sum-weighted-cache` at commit
`e1ae71db2231f172c6541820e2ce0a54aa14fc64` was recorded **Lean Verified** on
2026-11-02 (receipt 22:47:11 UTC) and its issue (#99) closed on that receipt.
It proves `Race.bound`:

```lean
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((384055881637 : Rat) / 200000000000)
```

`EndStatement.ThreeSum` is the verifier's trusted 3SUM problem
(`challenges/3sum-apsp/EndStatement.lean`, profile `3sum` in
`profiles/direct.json`): a length `n` is a vector of `n` integers, and the
answer is `yes` iff there are three **distinct positions** `i j k` with
`x i + x j + x k = 0`; no output condition is imposed.
`Problem.SolvedInTime Q r` is the trusted for-every-κ word-RAM statement: for
every `κ` there are one program `P`, a word-size coefficient `b` and a step
bound `T` with `BigO T r`, and for every instance whose entries satisfy
`|a| ≤ n^κ`, every word size `W ≥ b·(⌊log₂n⌋+1)` makes `P` halt within `T n`
steps with the right verdict and output. `BigO T r` is
`∃ K, ∀ n ≥ 2, T n ^ r.den ≤ K · n ^ r.num.toNat`; at
`r = 384055881637/200000000000` (already in lowest terms, `gcd = 1`) that is
`T n ^ 200000000000 ≤ K · n ^ 384055881637`.

The claim therefore reads: deterministic word-RAM 3SUM with distinct positions
and `n^κ`-bounded magnitudes runs in `O(n^1.920279408185)` time. This is
strictly below the profile's exponent cap of 2, strictly below the paper's own
Theorem 22 exponent `9996/5000 = 1.9992`, strictly below the previously Lean
Verified `96013971/50000000` (issue #92, replayed in this repository's
2026-11-01 audit), and strictly below the previous 3SUM record
`4800698571997281331/2500000000000000000 ≈ 1.92027942879891`, which the
submission still carries unchanged as the legacy ternary target in
`Submission/ThreeSum/TernaryParameters.lean`.

The commit is a single-commit delta from the commit the 2026-11-01 audit
replayed (`ac885d10`): *Improve 3SUM exponent and certify weighted-cache
optimization limit*, 578 files changed (494 added, 84 modified; +241,408 /
−1,280 lines), mostly a new `Submission/Optimality/` tree. The submission also
states an optimization barrier alongside the bound —
`Race.cache_optimum_interval` places `CacheOptimality.optimum` in
`[96013970409/50000000000, 2400349260231/1250000000000)`. This audit replays
the upper bound (`Race.bound`) only; the barrier claim is outside the
replayed target.

## Independent check

Local replay on the user's machine (Apple M4 Max, 16 cores, 128 GB RAM,
macOS 26.6.2):

- Cloned the submission repo at the pinned SHA, read-only (1,597 tracked files;
  1,568 admitted Lean modules — `Submission.lean` plus the `Submission/` tree,
  31,233,560 bytes, largest admitted file 287,594 bytes,
  `Submission/Optimality/Data/Complete.lean` — inside the verifier's 20 MB per
  file and 150 MB total caps).
- **The tracked statement module is the trusted bytes, not a copy of them.** The
  blob at `HEAD:Submission/EndStatement.lean` (git blob
  `b2e03ddc7dc78c273aa5a1edda073fd2274d87de` — the same blob id the 2026-11-01
  audit recorded, the file being unchanged since) is 7,255 bytes with zero CR
  bytes and sha256
  `4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987`, which is
  exactly the digest `profiles/direct.json` pins for
  `challenges/3sum-apsp/EndStatement.lean`, and equal to the trusted file's bytes
  in `bigospeedrun/verifier` (re-verified unchanged at main `34dda832` when this
  package was assembled). There is no definitional slack available *in the
  statement module at all*, because any weakening or substitution would change
  the bytes.
  - The environment note the 2026-11-01 audit recorded still applies, and this
    run hit it live. This machine sets `core.autocrlf=true`, so a plain
    `git clone`/`git checkout` here writes the working-tree copy as CRLF
    (7,394 bytes, sha256 `141b77e2…`) from that same LF blob — and the
    verifier's own `scripts/submissions.py:resolve_request`, run against such a
    checkout, refuses with `Trusted statement bytes changed`, a false alarm in
    exactly the direction PR #102 documented. This audit therefore compares the
    **blob**, not the checkout, stages with `core.autocrlf=false`, and re-ran
    `challenge_source` against a blob-bytes root. The distinction is immaterial
    to the result — Lean reads CRLF identically, and the verifier never uses
    the submission's copy as its target anyway, staging its own
    `profiles/direct.json` challenge as `VerifierChallenge.lean`.
- Staged the verifier's own layout exactly as `scripts/verifier.py:prepare`
  prepares it: `Submission.lean` + `Submission/`, `VerifierChallenge.lean` =
  the trusted challenge bytes plus the verifier-generated `Race.bound` target at
  the submitted bound, and `VerifierAudit.lean` = `import Submission` +
  `#print axioms Race.bound`, with the verifier's `lakefile.toml` shape (three
  `lean_lib`s: `Submission`, `VerifierChallenge`, `VerifierAudit`), Lean
  `v4.33.1`, and mathlib `0df444a3` from
  `profiles/anthropic-lake-manifest.json`, restored from a warm local cache of
  the same pins (all nine dependency revisions of the submission's own
  `lake-manifest.json` match; `verify.py` asserts the mathlib pin before
  building).
- **Independent confirmation that the staged target is the target the verifier
  would generate**: re-running `scripts/submissions.py:challenge_source` on the
  reduced submitted bound `384055881637/200000000000` produces a
  `VerifierChallenge.lean` byte-identical to the staged file (sha256
  `72c158d7acac8f7a3acc2a9d59bb9ce9623b5a960e5817ca35928569072689ec`). The
  generator's `Fraction(bound).as_integer_ratio()` is a no-op here because the
  bound is already reduced, so the target is stated at exactly
  `((384055881637 : Rat) / 200000000000)`.
- `lake build VerifierAudit VerifierChallenge` completed the full **5,022-job**
  schedule — 1,568 submission modules compiled from source, mathlib satisfied
  from cache — in 2,256 s, no errors, 930 warning lines (789 style and
  unused-variable linter warnings originating in submission modules plus 137 of
  their Hint/Note continuation lines, 3 Lake notices about the warm package
  clones, and the one expected `declaration uses 'sorry'` on the
  verifier-generated target at `VerifierChallenge.lean:142:8`). No `sorry`
  warning originates in a submission module.
- `'Race.bound' depends on axioms: [propext, Classical.choice, Quot.sound]` —
  within the verifier's permitted set. The development's own 62 embedded
  `#print axioms` self-checks (44 at the previous commit) all report the same
  triple — 63 axiom outputs appear in the build log and not one deviates — as do
  `ThreeSum.optimized_solvedInTime_384055881637_200000000000` (the theorem
  behind the wrapper) and
  `ThreeSum.WeightedGlobalOversizePrime.nativePrime_eq_selected`, which reads
  the development's single `opaque` package — so the closure is measured
  *through* that opaque body, not around it.
- `code/Scope.lean` compiled against the staged build with `lake env lean`
  (exit 0) and adds these probes on top of the verbatim-target discharge:
  `gcd 384055881637 200000000000 = 1` (so `r.den = 200000000000` and
  `r.num = 384055881637` are the integers the `BigO` exponents actually use);
  the bound is `< 2`, `< 9996/5000`, `< 96013971/50000000` and
  `< 4800698571997281331/2500000000000000000`; `ThreeSum.yes` and
  `ThreeSum.output` are restated by `Iff.rfl`; `SolvedInTime` is restated by
  `rfl` in its full `∀ κ / n^κ / b·(⌊log₂n⌋+1)` form; and the development's own
  certificate chain is probed — `WeightedGlobalParameters.targetExponent`
  equals the bound by `rfl`, while its `all_costs_lt_target` and
  `certificate_lt_target` are instantiated as proofs that every cost-ledger
  entry and the certificate exponent sit strictly below the bound. Any
  weakening of the quantity would break these elaborations.
- `code/OpaqueControl.lean` is a positive control for the audit method itself:
  it shows `#print axioms` reports `sorryAx` for an `opaque` whose body is
  `sorry` (both `controlViaOpaque` and `controlDirect` do, and the two sorry
  warnings the control arm emits are the control itself). The development's
  `opaque nativePrimeData` therefore cannot be concealing an unproved step
  behind a clean-looking closure.
- The submission's own certificate agrees with the stated bound rather than
  rounding past it, in the same direction the 2026-11-01 audit checked:
  `WeightedGlobalParameters.all_costs_lt_target` proves every entry of the
  six-element cost ledger (`2·bankEntropy/Hpi`,
  `2 − partitionEntropy/Hpi + 2·queryEntropy/Hpi`, `2·Halpha/Hpi`,
  `1 + partitionEntropy/Hpi`, `2 − partitionEntropy/Hpi`, `1`) is
  `< targetExponent := 384055881637/200000000000`, and `certificate_lt_target`
  proves `certificateExponent := 2400349260231/1250000000000 <
  targetExponent` — the bound exceeds its own certificate by 2×10⁻¹³, the
  top of the six-term infimum interval the commit message advertises. An
  independent exact-rational recomputation outside the build confirms
  `certificate < bound < 96013971/50000000 <
  4800698571997281331/2500000000000000000 < 9996/5000 < 2` with `gcd = 1`,
  and the development separately proves its certificate value below the prior
  record itself (`WeightedCacheParameters.target_lt_record`,
  `Submission/Weighted/Parameters.lean:431`).

### Shape of the claim

`Submission.lean:Race.bound` → `WeightedRace.bound` (`Submission/Weighted.lean`)
→ `ThreeSum.optimized_solvedInTime_384055881637_200000000000`
(`Submission/Weighted/Global/TernaryFinalSolver.lean`) →
`TernaryEndBridge.endStatement_of_solvers`
(`Submission/ThreeSum/TernaryEndBridge.lean`), which reduces the obligation to
`ThreeSumApsp.WordRam.SolvedInTime EndStatement.ThreeSum (r : ℝ) 0` and the
inherited `.endStatement rfl hr` bridge. The conclusion is *literally* the
trusted proposition, so the whole development upstream of that bridge can only
imply it — it has no way to weaken it from below.

## Reservations

- The build used a warm mathlib cache at the same pinned revision, so
  job-level timing reflects the submission modules only. The 5,022 figure is
  Lake's full schedule including cached dependency jobs.
- The verifier's Comparator byte-export and its `nanoda` replay were **not**
  run locally. The claim above that the statement module is the trusted bytes is
  exact and does not depend on the comparator, but the verifier's independent
  second kernel was not reproduced here; this audit rests on Lean's kernel
  alone.
- `Submission/PaperStatements.lean` (238 KB), the inherited
  `Submission/ThreeSumApsp/**` formalization, and the 494 files this commit
  adds — including the generated region-data tree under
  `Submission/Optimality/Data/` — are on the import path of the final bridge
  but were not read line by line. The guarantee this audit gives about them is
  kernel-deep only: whatever they state, the built proof infers the trusted
  proposition. `PROVENANCE.md` says the finite region data are generator
  proposals that "the final Lean proofs do not trust"; this audit checks the
  kernel-checked result, not the generator.
- Issue #99 carries no derivation report — its body is the bare submission
  form. The repository's `PROVENANCE.md` attributes the parameter refinement
  and the optimization certificate to Jionghan Wang, records that the complete
  solver builds on `proof-factory/3sum-bound` at `8af82141` (contributors
  including c0ldzy17, JoshuaWharton and HrishikSaiBojnal), and preserves the
  Anthropic, PBC benchmark-semantics notices and the inherited Alman–
  Vassilevska Williams record. I did not audit provenance beyond those files.
  This audit covers the bound; it does not establish novelty, priority or
  authorship.
- `opaque nativePrimeData`
  (`Submission/Weighted/Global/TernaryOversizePrime.lean:91`) hides a finite
  prime search from the elaborator. Its type is a subtype carrying the prime
  together with its specification, the control arm shows the axiom probe
  traverses opaque bodies, and the theorem reading it reports the standard
  triple. It is not an unproved oracle — but it is a place where a reader must
  trust the kernel rather than their own unfolding.
- Whether `384055881637/200000000000` is an improvement the maintainers intend
  to rank on the 3SUM board is their decision; this audit replays the
  statement, not the ranking policy. The audit likewise does not re-derive the
  weighted-cache cost analysis's mathematical correctness beyond kernel
  checking it, and says nothing about the optimality-barrier claim, which the
  verifier's target does not include.

## Reproduce

```sh
python3 auto-research/audits/2026-11-03-wangjionghan-3sum-99-local/verify.py \
  [--packages-cache <warm .lake/packages for mathlib 0df444a3>] \
  [--verifier-root <bigospeedrun/verifier checkout>]
```

With no `--verifier-root`, the script takes the trusted challenge bytes from
the submission's own `Submission/EndStatement.lean` and refuses to continue
unless the sha256 of its tracked blob equals the profile-pinned
`4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987`. On a host
with `core.autocrlf=true`, pass `--verifier-root` only if the checkout's
**blob** (not working tree) is compared — the script does exactly that.

The script fetches the pinned commit, refuses any SHA mismatch, stages the
verifier's build layout, builds `VerifierChallenge` and `VerifierAudit`, prints
the axiom closure of `Race.bound`, and runs both the scope probe and the opaque
control arm. Exit 0 means every check passed.

The trust boundary is Lean's kernel, the three standard axioms, the pinned
mathlib revision, and the verifier's trusted challenge bytes.
