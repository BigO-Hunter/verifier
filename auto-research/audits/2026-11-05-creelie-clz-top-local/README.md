# Audit — critical-line-zeros top row, independent local rerun

Row: `critical-line-zeros` **top row** (claimed, 2026-10-19T17:39Z), κ* ≥ 0.6731134
(score 6731134/10000000), D. Bhattacharjee & U. Bhattacharya,
[zenodo.org/records/23480715](https://doi.org/10.5281/zenodo.23480715) (MIT).

Pins (artifact fetched to `/tmp/clz_zenodo_audit/`): Zenodo `23480715` file
`creelie/mh-phys-v1.0.0.zip` (5,822,744 B, md5 `8a575fec…`, sha256 `34d1a3bf…b1a693`);
`github.com/creelie/mh-phys` @ `a772d9962c6e075edbac2008274dba58b0e2980e` (tag `v1.0.0`,
commit time 17:39:32Z = the board row time). Claim: an asymptotic windowed bound
`liminf N₀ˢ(T,2T)/N(T,2T) ≥ (3125/3112)(H − 7/3200) = 0.6731133552…`, where H is the
Montgomery–Taylor constant; the ONE computational step is Proposition 11 (eight-zero window
inequality F₈ ≥ 13/3125 at μ₀ = 1/3200), certified by branch and bound in
round-toward-−∞ arithmetic over a 128-bit Arb table.

**VERDICT: PASS — the computational step reproduces exactly (both certificates match the
author's node counts to the node, on a different compiler and ISA); every control holds;
both negative controls reject. The hand proofs and the unrefereed AF framework are NOT
re-verified (see NOTICE.md — that is the row's real load-bearing risk).**

## Checklist

| # | Item | Verdict | Evidence |
|---|---|---|---|
| 1 | Artifact & pin integrity | **PASS** | zip md5+sha256 == Zenodo record; **all 56 files byte-identical** (git blob hashes) to `a772d9962` (`evidence/zip_blob_audit.log`); tag `v1.0.0` ls-remote verified. An apparent whole-tree text diff was the audit checkout's own `core.autocrlf=true` — retracted, blobs identical (same trap #138 documented). |
| 2 | Table rebuild (CI-identical) | **PASS** | `table.py 4000 80000` from source (python-flint 0.9.0, Arb 128-bit): rebuild **byte-identical** — `cmp` vs `w4000_80k.bin` (sha256 `fd9304e3…`) and vs `w4000.bin` 46k prefix (sha256 `8ea9e0208216cb99f4cdcbcaa160b75ba7e7c89058f4d0396392df4f3afa42d5` == README claim `8ea9e020…afa42d5`). ~1 s (`evidence/table_rebuild.log`). |
| 3 | Certificate 1 — the board row (μ₀=1/3200, F₈ ≥ 13/3125) | **PASS** | `bbp` (gcc-16, `-O2 -frounding-math -fopenmp`, 2 threads): **VERIFIED R=8, nodes = 10,039,560,518 — exact match** with the author's `bbp8_3200_final.log`; components `[3756,4877] [7080,53248]`, 222,858 work boxes, box-list checksum `d5746ef8030b2d5c` all identical. 374.9 s wall (author: 12 m 08 s) (`evidence/bbp_3200.log`). |
| 4 | Certificate 2 (μ₀=1/2000, F₈ ≥ 605/100000) | **PASS** | serial `bb`: **VERIFIED, nodes = 5,440,924,378 — exact match**; `initial_boxes=128`, `max_stack=144`, even the intermediate progress stack depths (68, 70, …) identical. 319.9 s (author: 9 m 57 s) (`evidence/bb_2000.log`). |
| 5 | Eigenvalue lemma (λmax ≤ 1/(δ₁K₀) < 2) | **PASS** | `eig_lemma.py` rerun **digit-for-digit identical** to shipped `eig_lemma.txt`: Arb bound `1.9790264618989043491392825446270941444` < 2, majorant endpoints negative, lattice λmax 1.979025 (sharpness) (`evidence/eig_lemma.log`). |
| 6 | Method ceiling | **PASS** | `chain_all.py` rerun: `max over all mu: 0.6735602` **exact match**, ≤ 0.67357 ✓; rotation-aware line-by-line comparison vs shipped `chain_all.txt`: 0 differences (`code/cmp_chain_all.py`, `evidence/cmp_chain_all.log`). 50 s. |
| 7 | Row identity, display rounding, ordering | **PASS** | mpmath dps=60: exact `0.67311335523719839104111081178030124175912097186924`; board display 0.6731134 = exact + **4.47628e-8** = correct 7-dp rounding, **not an error**; H = 0.6725007036794116457…; ordering ours > Jo `(1345000H−2680)/1340003 = 0.6730085279…` (+1.04827e-4) > H re-verified (`evidence/controls_mpmath.log`). |
| 8 | Negative controls | **PASS** | (a) **Over-claim T = 14/3125 REJECTED**: `FAIL box: 4144 4123 7866 4180 7866 4122 4144 lb=0.004479900828 < T`, RC=1, 291 s (`evidence/neg_T14.log`). (b) **Perturbed table REJECTED**: zeroing the rigorous lower bounds on the minimizer's r=1 gap cells (4160–4190, 7940–7960) → `FAIL box: 4177 7953 7945 7940 4160 4090 4160 lb=0.004159967975 < 13/3125`, RC=1, 0.5 s (`code/make_perturbed_table.py`, `evidence/neg_table.log`). (c) Four wrong-constant identities (7/3199, 1/3200, 3124/3112, 3125/3113) all fail to reproduce the row value. The certificate does not rubber-stamp. |
| 9 | Stale-row disclosure | **DISCLOSED** | Successor **v1.3.0** (Zenodo [23489033](https://doi.org/10.5281/zenodo.23489033), 2026-10-20, commit `aff473549…`, md5 `f2a3bff3…`) proves **0.6732896395** (ten-zero windows) — better than the board row — and is **not on the board**. Metadata verified; its math NOT audited (out of scope). |

## Discrepancies — none invalidate the row

- **D1 — environment deviation (disclosed):** the plan preferred an ubuntu+gcc container; the
  audit host's Docker daemon was not running, so the reruns used the sanctioned fallback:
  Homebrew **GCC 16.2.0** natively on **Apple M4 Max (arm64)** with the author's flags
  (`-O2 -frounding-math [-fopenmp]`; gcc honors `FENV_ACCESS`, Apple clang does not). The
  exact node-count/checksum matches show no FP-contraction drift on this toolchain. `evidence/env.txt`.
- **D2 — retracted before filing:** a whole-tree text mismatch zip-vs-clone was the audit
  checkout's `core.autocrlf=true`; raw blob hashes are identical (56/56). Not an artifact defect.
- **D3 — cosmetic:** `chain_all.py` rerun prints some patterns as different cyclic rotations
  (and constant words at ambiguous period); all numeric fields (gbar, E, bounds, max) identical.
- **D4 — successor not on board:** v1.3.0 (0.6732896395) supersedes the row's value; the row
  as deposited (v1.0.0) is nonetheless exactly what it claims to be.

## Honest limits

This audit certifies the **computational step only**. The hand proofs — the Fejér-majorant
eigenvalue lemma, stability + pinching, block decomposition, dyadic→global, Prop 11 ⇒ theorem —
rest on the **unrefereed** Alpöge–Furman rank–trace framework (arXiv:2608.13637, Lean-4
formalization claimed but not audited) and are NOT re-verified here. A broken hand lemma would
void the row regardless of this rerun. No zero database applies in principle (asymptotic bound).
Details in `NOTICE.md`.

## This PR

**Title:** `Audit: local rerun of the critical-line-zeros top row (creelie/mh-phys a772d99, Zenodo 23480715)`

Body: see `PR_DRAFT.md` (filed by the coordinator, not by this audit).

## File guide

| Path | Contents |
|---|---|
| `NOTICE.md` | attribution, honest limits, stale-row + env-deviation disclosures |
| `RESULT.json` | machine-readable verdict, pins, rerun numbers |
| `MANIFEST.json` | sha256 of every file in this package |
| `data/source.json` | Zenodo record(s), md5/sha256s, git pin, successor metadata |
| `data/record_*.json` | Zenodo API snapshots (23480715 row, 23489033 successor) |
| `evidence/maintainer-artifact.zip` | the deposited Zenodo artifact (md5+sha256 as recorded) |
| `evidence/zip_blob_audit.log` | 56/56 blob-hash identity zip ↔ git pin |
| `evidence/env.txt` | compiler, flags, FENV_ACCESS handling, host, deviation note |
| `evidence/table_rebuild.log` | rebuild + both CI cmp checks + shas |
| `evidence/bbp_3200.log`, `bb_2000.log` | the two certificate reruns (VERIFIED, exact nodes) |
| `evidence/eig_lemma.log`, `chain_all.log`, `chain_all_rerun.txt`, `cmp_chain_all.log` | lemma + ceiling reruns |
| `evidence/controls_mpmath.log` | 50-digit identity, rounding, ordering, wrong-constant negatives |
| `evidence/neg_T14.log`, `neg_table.log`, `make_perturbed_table.log` | negative controls (both REJECT) |
| `evidence/replay.sh` | full replay script (~30 min compute, ≤4 threads) |
| `code/` | controls_mpmath.py, cmp_chain_all.py, make_perturbed_table.py |
| `verify.py` | cheap network re-checks (Zenodo metadata, shas, exact value); `--full` pointer |
