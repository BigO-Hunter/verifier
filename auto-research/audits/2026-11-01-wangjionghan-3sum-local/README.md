# Independent local Lean replay: 3SUM exponent 96013971/50000000 (issue #92)

## Claim and scope

The pinned submission `Wang-jiong-han/3sum-weighted-cache` at commit
`ac885d10bdbf723c3e0549198f9345bedf2a4131` was recorded **Lean Verified** on
2026-11-01 and its issue (#92) closed on that receipt. It proves `Race.bound`:

```lean
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((96013971 : Rat) / 50000000)
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
`∃ K, ∀ n ≥ 2, T n ^ r.den ≤ K · n ^ r.num.toNat`; at `r = 96013971/50000000`
(already in lowest terms, `gcd = 1`) that is `T n ^ 50000000 ≤ K · n ^ 96013971`.

The claim therefore reads: deterministic word-RAM 3SUM with distinct positions
and `n^κ`-bounded magnitudes runs in `O(n^1.92027942)` time. This is strictly
below the profile's exponent cap of 2 and strictly below the previous 3SUM
record `4800698571997281331/2500000000000000000 ≈ 1.92027942879891`, which the
submission still carries unchanged in `Submission/ThreeSum/TernaryParameters.lean`.

## Independent check

Local replay on the user's machine (Apple M4 Max, 16 cores, 128 GB RAM,
macOS 26.6.2):

- Cloned the submission repo at the pinned SHA, read-only (1,103 tracked files;
  1,092 admitted Lean modules — `Submission.lean` plus the `Submission/` tree,
  8,049,566 bytes, largest file 237,988 bytes — inside the verifier's 20 MB per
  file and 150 MB total caps).
- **The tracked statement module is the trusted bytes, not a copy of them.** The
  blob at `HEAD:Submission/EndStatement.lean` (git blob
  `b2e03ddc7dc78c273aa5a1edda073fd2274d87de`) is 7,255 bytes with zero CR bytes
  and sha256
  `4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987`, which is
  exactly the digest `profiles/direct.json` pins for
  `challenges/3sum-apsp/EndStatement.lean`, and equal to the trusted file's bytes
  in `bigospeedrun/verifier`. This is stronger than a comment-stripped or
  whitespace-normalized comparison: there is no definitional slack available *in
  the statement module at all*, because any weakening or substitution would
  change the bytes.
  - One environment note, recorded because it flips a naive check. This machine
    sets `core.autocrlf=true`, so a plain `git clone`/`git checkout` here writes
    the working-tree copy as CRLF (7,394 bytes, sha256 `141b77e2…`) from that same
    LF blob. The verifier's Linux runner leaves `core.autocrlf` unset and gets
    the tracked bytes; this audit therefore compares the **blob**, not the
    checkout, and stages with `core.autocrlf=false`. The distinction is
    immaterial to the result — Lean reads CRLF identically, and the verifier
    never uses the submission's copy as its target anyway, staging its own
    `profiles/direct.json` challenge as `VerifierChallenge.lean` — but a
    working-tree digest comparison produces a false alarm in either direction.
    PR #97's DFT audit reported the same CRLF-only difference between a fork's
    tracked copy and the trusted bytes; on this evidence that is likely the same
    checkout artifact rather than a property of the fork, and it is worth
    re-checking at the blob level.
- Staged the verifier's own layout exactly as `scripts/verifier.py:prepare`
  prepares it: `Submission.lean` + `Submission/`, `VerifierChallenge.lean` =
  the trusted challenge bytes plus the verifier-generated `Race.bound` target at
  the submitted bound, and `VerifierAudit.lean` = `import Submission` +
  `#print axioms Race.bound`, with the verifier's `lakefile.toml` shape (three
  `lean_lib`s: `Submission`, `VerifierChallenge`, `VerifierAudit`), Lean
  `v4.33.1`, and mathlib `0df444a3` from
  `profiles/anthropic-lake-manifest.json`, restored from a warm local cache of
  the same pins.
- **Independent confirmation that the staged target is the target the verifier
  would generate**: re-running `scripts/submissions.py:challenge_source` on the
  reduced submitted bound `96013971/50000000` produces a
  `VerifierChallenge.lean` byte-identical to the staged file (sha256
  `26ac8aab575031cc901110cad191514b3458f1298d5b37ce9b297bc95b0da0c2`). The
  generator's `Fraction(bound).as_integer_ratio()` is a no-op here because the
  bound is already reduced, so the target is stated at exactly
  `((96013971 : Rat) / 50000000)`.
- `lake build VerifierAudit VerifierChallenge` completed the full **4,546-job**
  schedule — 1,092 submission modules compiled from source, mathlib satisfied
  from cache — in 686 s, no errors, 780 warning lines (775 style and
  unused-variable warnings originating in submission modules, 2 Lake notices
  about the warm package clone, 2 manifest `inputRev` notices, and the one
  expected `declaration uses 'sorry'` on the verifier-generated target at
  `VerifierChallenge.lean:142`). No `sorry` warning originates in a submission
  module. A separate manual staging run of the same layout produced the same job
  count, the same 775 submission warnings, and no errors.
- `'Race.bound' depends on axioms: [propext, Classical.choice, Quot.sound]` —
  within the verifier's permitted set. The development's own 44 embedded
  `#print axioms` self-checks all report the same triple, as do
  `ThreeSum.weighted_solvedInTime_96013971_50000000` (the theorem behind the
  wrapper) and `ThreeSum.WeightedGlobalOversizePrime.nativePrime_eq_selected`,
  which reads the development's single `opaque` package — so the closure is
  measured *through* that opaque body, not around it.
- `code/Scope.lean` compiled against the staged build with `lake env lean`
  (exit 0) and adds these probes on top of the verbatim-target discharge:
  `gcd 96013971 50000000 = 1` (so `r.den = 50000000` and `r.num = 96013971` are
  the integers the `BigO` exponents actually use); the bound is `< 2` and
  `< 9996/5000` (the paper's own Theorem 22 exponent `1.9992`); the bound is
  `< 4800698571997281331/2500000000000000000`; `ThreeSum.yes` and
  `ThreeSum.output` are restated by `Iff.rfl`; and `SolvedInTime` is restated by
  `rfl` in its full `∀ κ / n^κ / b·(⌊log₂n⌋+1)` form. Any weakening of the
  quantity would break these elaborations.
- `code/OpaqueControl.lean` is a positive control for the audit method itself:
  it shows `#print axioms` reports `sorryAx` for an `opaque` whose body is
  `sorry`. The development's `opaque nativePrimeData` therefore cannot be
  concealing an unproved step behind a clean-looking closure.
- The submission's own certificate agrees with the stated bound rather than
  rounding past it: `WeightedCacheParameters.proposed_ledger_lt_target` proves
  every entry of its six-element cost ledger (`2Bn/Hn`, `(2Hn−Gn+2Qn)/Hn`,
  `2An/Hn`, `(Hn+Gn)/Hn`, `(2Hn−Gn)/Hn`, `1`) is `< targetExponent` with
  `targetExponent := 96013971/50000000`, and `target_lt_record` proves
  `96013971/50000000 < 4800698571997281331/2500000000000000000`.

### Shape of the claim

`Submission.lean:Race.bound` → `WeightedRace.bound` (`Submission/Weighted.lean`)
→ `ThreeSum.weighted_solvedInTime_96013971_50000000`
(`Submission/Weighted/Global/TernaryFinalSolver.lean`) →
`TernaryEndBridge.endStatement_of_solvers`
(`Submission/ThreeSum/TernaryEndBridge.lean`), which reduces the obligation to
`ThreeSumApsp.WordRam.SolvedInTime EndStatement.ThreeSum (r : ℝ) 0` and the
inherited `.endStatement rfl hr` bridge. The conclusion is *literally* the
trusted proposition, so the whole development upstream of that bridge can only
imply it — it has no way to weaken it from below.

## Reservations

- The build used a warm mathlib cache at the same pinned revision, so
  job-level timing reflects the submission modules only. The 4,546 figure is
  Lake's full schedule including cached dependency jobs.
- The verifier's Comparator byte-export and its `nanoda` replay were **not**
  run locally. The claim above that the statement module is the trusted bytes is
  exact and does not depend on the comparator, but the verifier's independent
  second kernel was not reproduced here; this audit rests on Lean's kernel
  alone.
- `Submission/PaperStatements.lean` (238 KB) and the inherited
  `Submission/ThreeSumApsp/**` formalization are on the import path of the final
  bridge but were not read line by line. The guarantee this audit gives about
  them is kernel-deep only: whatever they state, the built proof infers the
  trusted proposition.
- The issue's own derivation report records 784 of 1,096 source files identical
  to `direct-issue-35`, a previously verified submission by another author, and
  the README credits `proof-factory/3sum-bound`, c0ldzy17, Joshua Wharton and
  Hrishik Sai Bojnal while retaining the upstream LICENSE and NOTICE. I did not
  audit provenance beyond that report. This audit covers the bound; it does not
  establish novelty, priority or authorship.
- `opaque nativePrimeData` (`Submission/Weighted/Global/TernaryOversizePrime.lean`)
  hides a finite prime search from the elaborator. Its type is a subtype
  carrying `LocalCoverBounds.selectedPrime` together with that function's
  specification, the control arm shows the axiom probe traverses opaque bodies,
  and the theorem reading it reports the standard triple. It is not an unproved
  oracle — but it is a place where a reader must trust the kernel rather than
  their own unfolding.
- Whether `96013971/50000000` is an improvement the maintainers intend to rank
  on the 3SUM board is their decision; this audit replays the statement, not the
  ranking policy. The audit likewise does not re-derive the weighted-cache cost
  analysis's mathematical correctness beyond kernel checking it.

## Reproduce

```sh
python3 auto-research/audits/2026-11-01-wangjionghan-3sum-local/verify.py \
  [--packages-cache <warm .lake/packages for mathlib 0df444a3>] \
  [--verifier-root <bigospeedrun/verifier checkout>]
```

With no `--verifier-root`, the script takes the trusted challenge bytes from
the submission's own `Submission/EndStatement.lean` and refuses to continue
unless its sha256 equals the profile-pinned
`4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987`.

The script fetches the pinned commit, refuses any SHA mismatch, stages the
verifier's build layout, builds `VerifierChallenge` and `VerifierAudit`, prints
the axiom closure of `Race.bound`, and runs both the scope probe and the opaque
control arm. Exit 0 means every check passed.

The trust boundary is Lean's kernel, the three standard axioms, the pinned
mathlib revision, and the verifier's trusted challenge bytes.
