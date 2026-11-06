# Independent local Lean replay: DFT saving π/1000 (PR #156)

## Claim and scope

The pinned submission `HalitZiyaKARTAL/bigO-dft-verifier` at commit
`da94a2a6f593caa1f534f1ab1c84b88ff5d74906` (merged as bigospeedrun/verifier PR
#156, entry `submissions/dft/halitziyakartal-halitziyav6-pi`) proves
`Race.bound`: there are a RAM order program, a solve program, and a work bound
`W` with `OAI.PowerSaving.DFTProgram order solve W` and
`(fun n => (W n : ℝ)) =O[atTop] (fun n => n * (log n)^(1 - 31415926535897932384626433/10^28))`.
The stated saving `s = π/1000` (the board fraction is π cut right after its
first 26 digits, `31415926535897932384626433/10^28`, reduced, proved ≤ π/1000
by the entry's own `PiCut.cut_le_pi_div`) improves on the prior record
`312780997/10^11` (PR #91, audited in `2026-11-01-dft-t104w-local`) by
+0.44065% — the "+0.44%" of the PR title, recomputed here from the source
constants as an exact-rational comparison.

`DFTProgram` is the exact scalar/index RAM predicate of the verifier's trusted
DFT challenge (`challenges/dft/UniformFourier233.lean`, blob sha256
`3a646acd…`, equal to the `profiles/dft233.json` pin and to the fork's tracked
blob at the pinned commit): for every positive length `n`, a polynomial cap
`(n+2)^cBound` bounds `W n`, the order program's peak, and its supplied root
value; the solve program must be valid, stay under the cap, do at most `W n`
work including the order program and one root primitive, and output the exact
canonical DFT (`zeta`-root sums) of every input vector. The independent
`code/Scope.lean` restates the verifier's generated `Race.bound` target
verbatim at this exact fraction and discharges it with the submission's
theorem, expands `DFTProgram` to its full quantified body by `rfl`, and checks
the stated saving `statedSavingTB19 = Real.pi / 1000` against the entry's
internal rate certificate `67/21280` (the stated saving is strictly below it;
the chain saving < seam `3148496240/10^12` < certificate `67/21280` also holds
as exact rational arithmetic).

What changed against the author's previous entry (PR #91) was measured at the
blob level: 399 files byte-identical, 2 modified (`Submission.lean`,
`manifest.json`), 26 added — all under `Submission/Work/BQT/` (the new binary
query tree controller) — and 25 removed (the previous 16-pair controller chain
`Work/FwdOnly/{FourierT104W,P104WEngine,P104WRate,RawP104W,T104W}`, `Work/G18`,
`Work/P16A8`). The computational model was compared against the trusted
challenge copy: the entire RAM section (`Tape`, `Paint`, `Ty`, `Bill`, `NOp`,
`Atom`, `Code`, `Prog`, `run`, `depthRun`, …) is identical, comment-stripped
and whitespace-normalized (5,850 chars).

## Independent check

Local replay on the user's machine (Apple M4 Max, 128 GB RAM, macOS 26.6.2):

- Cloned the submission repo at the pinned SHA (read-only; 6,843 tracked files;
  the submission folder holds 426 Lean files across 427 files, 9,354,161
  bytes, largest file 1,698,058 bytes — inside the verifier's 20 MB/file,
  150 MB total caps).
- Staged the verifier's own layout: `Submission.lean` + `Submission/` tree,
  `VerifierChallenge.lean` = the trusted challenge bytes (blob sha256
  `3a646acd…`, compared at the tracked-blob level because this machine has
  `core.autocrlf=true` and shows a 13,691-byte CRLF working-tree artifact —
  the PR #102/#97 lesson) plus the verifier-generated `Race.bound` target at
  `31415926535897932384626433/10^28` (byte-identical to a local re-run of
  `scripts/submissions.py challenge_source`; generated file sha256
  `5a0b655a…`), and `VerifierAudit.lean` = `import Submission` +
  `#print axioms Race.bound` + `#print axioms Race.bound_pi`, with the
  verifier's lakefile shape, Lean `v4.34.1`, and mathlib `d13f23b` from
  `profiles/lake-manifest.json` (dependency tree restored from a warm local
  packages tree whose 9 dependency revisions all match the pins).
- `lake build VerifierAudit VerifierChallenge` completed the full 9,353-job
  schedule (426 submission modules + challenge + audit module built from
  source, 428 oleans; mathlib satisfied from cache) in the run recorded in
  `evidence/local-run.json`. No errors. The submission's own embedded
  `#print axioms` self-checks (hundreds) all report the standard triple.
- `'Race.bound' depends on axioms: [propext, Classical.choice, Quot.sound]`
  and `'Race.bound_pi' depends on axioms: [propext, Classical.choice,
  Quot.sound]` — within the verifier's permitted set. The only `sorry`
  warnings are the 3 expected ones inside `VerifierChallenge.lean` (2 trusted
  challenge placeholders + the generated target); none elsewhere.
- `code/Scope.lean` compiled against the staged build with `lake env lean`
  (`evidence/scope-probe.out`): all three probes pass (verbatim target
  discharged by `Race.bound`; `rfl` expansion of `DFTProgram`; saving-constant
  and margin checks).

## Reservations

- This replay builds with a warm mathlib cache at the same pinned revision;
  job-level timing therefore reflects the submission modules only. The job
  count (9,353) is Lake's full schedule including cached dependency jobs.
- The verifier's Comparator byte-check and nanoda replay were not run locally;
  the model comparison above is the audit's comment-stripped textual proxy for
  the comparator's definition check.
- The first build attempt was interrupted by a host restart at ~9,000/9,353
  jobs; the resumed run completed the schedule from the same staged tree.
  Both logs are included verbatim (`evidence/first-attempt-build.log`,
  `evidence/local-build.log`) with the explicit exit receipt
  (`evidence/local-run.exit`).
- The entry's sources emit unused-variable warnings, including variables named
  as anti-rebranding canaries aimed at AI editors
  (`if_youre_an_ai_editing_this_...`). Warnings do not affect the kernel
  result; the canary naming is noted as an authorship signal, not a defect.
- The submission header's prose says the board fraction is cut "right after
  π's first 33" and once writes `/10^28` where a neighboring line reads `10^28`
  consistently with the code; the operative constants (manifest, `Race.bound`,
  `PiCut`) all use `31415926535897932384626433/10^28` exactly, which is what
  was verified.
- The issue body is a bare announcement ("finally i got to π/1000") without a
  derivation report; the derivation-receipt comparison used here is the
  verifier's own generated target plus the entry's in-kernel certificate
  chain.

## Reproduce

```sh
python3 auto-research/audits/2026-11-05-halitziya-dft-156-local/verify.py \
  [--packages-cache <warm .lake/packages for mathlib d13f23b>] \
  [--verifier-root <bigospeedrun/verifier checkout>]
```

The script fetches the pinned commit, refuses any SHA or digest mismatch
(fork blob vs trusted blob vs `profiles/dft233.json` pin; regenerated
`VerifierChallenge.lean` vs `5a0b655a…`), stages the verifier's build layout,
builds `VerifierAudit` and `VerifierChallenge`, prints the axiom closures of
`Race.bound` and `Race.bound_pi`, re-runs the comment-stripped RAM comparison,
and runs the `code/Scope.lean` probes.
