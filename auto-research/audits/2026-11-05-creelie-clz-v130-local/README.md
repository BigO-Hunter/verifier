# Audit — critical-line-zeros successor v1.3.0, independent local rerun

Row: `critical-line-zeros` **successor release v1.3.0** (published 2026-10-20T03:35Z), claimed
κ* ≥ 0.6732896395 (ten-zero windows), D. Bhattacharjee & U. Bhattacharya,
[zenodo.org/records/23489033](https://doi.org/10.5281/zenodo.23489033) (MIT).

This is the *successor* of the row audited in
[`../2026-11-05-creelie-clz-top-local/`](../2026-11-05-creelie-clz-top-local/), which proved
0.6731133552 for release v1.0.0 and disclosed v1.3.0 as **not audited**. This package audits
v1.3.0. **The v1.3.0 result is not on the board**: at the audit snapshot the row still lists
release v1.0.0 (`current.source = https://zenodo.org/records/23480715`, κ* ≥ 0.673113), and
Zenodo 23489033 appears nowhere in `chat-knowledge.json` (`data/board_row_snapshot.json`).

Pins: Zenodo `23489033`, file `creelie/mh-phys-v1.3.0.zip` (9,126,044 B,
md5 `f2a3bff3d553b36f7c5647bd71ab92ef`, sha256 `5afc161e…b13798ac2`);
`github.com/creelie/mh-phys` @ `aff473549ca8cacf6b6b890cacf67e8d3d458934` (tag `v1.3.0`,
ls-remote verified; commit time 2026-10-20T03:34:49Z, 23 s before the Zenodo record).
Claim: κ* ≥ (H_MT − μ)/(1 − c₀) = (125000/124111)(H_MT − 7999/2000000) = 0.6732896395962199…,
where H_MT = 1.5 − cot(1/√2)/√2, μ = 7999/2000000 is the linear total of the ten-zero weights,
and c₀ = 889/125000 is the certified window constant. The ONE new computational step is the
ten-zero window inequality F₁₀ ≥ 889/125000 (Proposition 11), certified by branch and bound with
two lower bounds (a cell table and a second-order Taylor bound from tables of w, w′ and w″), in
128-bit ball arithmetic.

**VERDICT: PASS — the computational step reproduces exactly (same node count as the author:
1,424,333,714, same 207,518 work boxes, same box-list checksum `bb2e8f8af3a7efd2`); the tables
rebuild (kernel table byte-identical, second-order table identical up to six 1e-18 cell bounds, see
D1); the eigenvalue lemma, the ten-zero ceiling and the method ceiling all reproduce; the author's
stated negative control (target 0.0071125) still fails at a single cell. The hand proofs and the
unrefereed Alpöge–Furman framework are NOT re-verified (see NOTICE.md — that is the claim's real
load-bearing risk).**

## Checklist

| # | Item | Verdict | Evidence |
|---|---|---|---|
| 1 | Artifact & pin integrity | **PASS** | zip size/md5 == Zenodo record; **all 84 files byte-identical** (git blob hashes) to `aff473549` (`evidence/zip_blob_audit.log`); tag `v1.3.0` ls-remote verified; commit time 03:34:49Z matches the record's 03:35:12Z. |
| 2 | Kernel table rebuild (`table.py 4000 80000`) | **PASS** | rebuild **byte-identical**: 80k sha256 `fd9304e3…` and 46k prefix `8ea9e020…afa42d5` == `w4000.bin`, both == the README claims (`evidence/table_rebuild.log`). |
| 3 | Second-order table rebuild (`dtable.py 4000 80000 4`) | **PASS with D1** | shipped `d4000_80k.bin` sha256 `8915be68…baca14c105` == README claim; the platform rebuild is deterministic but differs from the shipped file in **6 of 320,003 doubles** (all w″ cell lower bounds, abs ≤ 1.8e-18, rel ≤ 1.9e-9). Both values are valid lower bounds at those cells (100-digit check, `evidence/w2_cell_check.log`) and the certificate is unchanged with either table (`evidence/dtable_diff.log`). |
| 4 | Certificate — ten-zero window inequality (μ = 7999/2000000, F₁₀ ≥ 889/125000) | **PASS** | `bbp_cf` (Homebrew gcc 16.2.0, `-O2 -frounding-math -fopenmp`, 4 threads): **VERIFIED R=10, nodes = 1,424,333,714 — exact match** with the author's shipped `verify/bbpcf10.log`; presplit components, 207,518 work boxes and checksum `bb2e8f8af3a7efd2` identical; 3 m 39 s (author: 2 m 48 s) (`evidence/bbp_cf_shipped.log`). Re-run with the platform-rebuilt second-order table: VERIFIED, **same node count**, same checksum (`evidence/bbp_cf_rebuilt_dtable.log`). |
| 5 | Eigenvalue lemma (λmax ≤ 1/(δ₁K₀) < 2) | **PASS** | `checks/eig_lemma.py` rerun **digit-for-digit identical** to the shipped `checks/eig_lemma.txt` (both 823 B; `diff` empty). Bound `1.9790264618989043491392825446270941444` < 2, majorant endpoints negative, lattice λmax 1.979025 (`evidence/eig_lemma_rerun.log`). |
| 6 | Ten-zero weight ceiling | **PASS** | `checks/chain_window.py 4 0.0015,…,0.005 9` reproduces `checks/chain_window10.txt` **exactly** (7/7 rows): max 0.6732908 at μ = 0.004, so the claimed 0.6732896396 is below the ceiling of the weights used (`evidence/chain_window10_rerun.txt`). |
| 7 | Method ceiling | **PASS** | `checks/chain_all.py` rerun: **max over all mu = 0.6735602 — exact match**, ≤ 0.67357 ✓; rotation-aware line-by-line comparison vs shipped `checks/chain_all.txt`: **123/123 rows, 0 non-rotation differences** (`evidence/cmp_chain_all.log`). |
| 8 | Arithmetic of the claim | **PASS with D2** | mpmath dps=60: `(H−μ)/(1−c₀)` == `(125000/124111)(H−7999/2000000)` == `0.673289639596219962104869623566097272394673949756935403519419`; weights file's b-sum is exactly 7999/2000000; paper condition `11c₀ = 0.078232 < 0.4794 < (4/3)w(11/20) = 0.4794187462…` holds; the paper's printed `0.6732896395962199` and the claimed `0.6732896395` are **truncations** (10-dp rounding would be `…96`), i.e. conservative, not overclaims (`evidence/controls_mpmath.log`, `code/controls_mpmath.py`). |
| 9 | Negative control | **PASS** | the author's own stated over-claim **T = 0.0071125 REJECTED**: `FAIL box: 7902 4157 7900 4158 7899 4158 7898 4157 7902 lb=0.007112482972 < T`, RC=1 (`evidence/neg_T0.0071125.log`). The certificate does not rubber-stamp: the exact minimum of F for these rounded weights is 0.0071126, so the certified 0.007112 sits 6e-7 below it and 0.0071125 is 1.7e-8 above the failing box's bound. |
| 10 | Stale-row status | **DISCLOSED** | v1.3.0 (0.6732896395) is strictly better than the listed row's 0.6731134 and is **not on the board**; this audit does not list it. Board listing is the maintainers' decision. |

## Discrepancies — none invalidate the claim

- **D1 — second-order table rebuild is not byte-identical on this host (disclosed, measured).**
  `verify/dtable.py` with the pinned `python-flint==0.9.0` reproduces `d4000_80k.bin` byte-for-byte
  in the author's Linux CI (`cmp` step in `.github/workflows/verify.yml`) but on this arm64/macOS host
  yields **6 differing doubles of 320,003** (all in the w″ cell-bound segment), deterministic across
  three runs. The differences are ≤ 1.8e-18 (relative ≤ 1.9e-9). Both the shipped and the rebuilt
  value are valid lower bounds at each affected cell (checked against a 100-digit mpmath sampling of
  the cell minimum; the tables are otherwise tight, sampled/stored ratios 0.9993–1.0002), and the
  ten-zero certificate **verifies with both, with the identical node count and box checksum**. The
  cause (Arb/MPFR endpoint variation across platform builds) was not isolated; this is a
  reproducibility deviation, not a soundness defect.
- **D2 — display is truncated, not rounded.** The claimed 0.6732896395 and the paper's
  0.6732896395962199 are 10- and 16-digit **truncations** of 0.67328963959621996…; correct rounding
  gives 0.6732896396 (resp. …962200). The claim therefore *understates* the exact bound by 9.6e-11.
  No overclaim; recorded because the previous audit checked (and found correct) *rounding* of the
  v1.0.0 display, and a future reader should not mistake truncation for a rounding error.
- **D3 — earlier certificates not re-run.** The artifact also ships the weighted nine-zero
  (F₉ ≥ 7/1000, 52,891,178,741 nodes) and eight-zero (F₈ ≥ 19/4000, 21,067,790,614 nodes)
  certificates of releases 1.2.0/1.1.0, and the uniform eight-zero one already audited for v1.0.0.
  They support the earlier bounds 0.6732134/0.6731986, not the 0.6732896395 claim, and are out of
  scope here.

## Honest limits

This audit certifies the **computational step and the arithmetic of the claim only**. The hand
proofs — the Fejér-majorant eigenvalue lemma, stability + pinching, block decomposition,
dyadic→global, Prop 11 ⇒ theorem — rest on the **unrefereed** Alpöge–Furman rank–trace framework
(arXiv:2608.13637; Lean-4 formalization claimed, not audited) and are NOT re-verified here. This
package verifies the *algebraic* step from the certified inequality to the claimed number
(`(H−μ)/(1−c₀)` with exact μ, c₀ and the paper's condition) but **not** the block-decomposition
lemma that produces `(H−μ)/(1−c₀)` from the window inequality; a broken hand lemma would void the
claim regardless of this rerun. No zero database applies in principle (asymptotic bound). Details in
`NOTICE.md`.

## This PR

**Title:** `Audit: local rerun of critical-line-zeros v1.3.0 (creelie/mh-phys aff4735, Zenodo 23489033)`

Adds only this folder under `auto-research/audits/`. No third-party binaries: the deposited zip is
pinned by id/size/md5/sha256 and is not included (per the #151 maintainer rule).

## File guide

| Path | Contents |
|---|---|
| `NOTICE.md` | attribution, scope, honest limits, AI-assistance disclosure |
| `RESULT.json` | machine-readable verdict, pins, rerun numbers |
| `MANIFEST.json` | sha256 of every file in this package |
| `data/source.json` | Zenodo record, md5/sha256/sha256-of-zip, git pin, table shas, board status |
| `data/record_23489033.json` | Zenodo API snapshot fetched during this audit |
| `data/board_row_snapshot.json` | site row + board timestamp showing v1.3.0 unlisted |
| `evidence/env.txt` | host, compiler, flags, python/flint versions, load |
| `evidence/zip_blob_audit.log` | 84/84 blob-hash identity zip ↔ git pin |
| `evidence/table_rebuild.log`, `dtable_rebuild.log` | kernel + second-order rebuilds and comparisons |
| `evidence/dtable_diff.log`, `w2_cell_check.log` | the six differing w″ cells: values, magnitudes, validity |
| `evidence/bbp_cf_shipped.log`, `bbp_cf_rebuilt_dtable.log` | the ten-zero certificate with the shipped and the rebuilt table |
| `evidence/neg_T0.0071125.log` | negative control (over-claim REJECTED) |
| `evidence/eig_lemma_rerun.log`, `chain_window10_rerun.txt` | lemma + ten-zero ceiling reruns |
| `evidence/chain_all_rerun.txt`, `cmp_chain_all.log` | method-ceiling rerun + rotation-aware comparison |
| `evidence/controls_mpmath.log` | 60-digit identity, truncation check, condition, orderings |
| `evidence/replay.sh` | full local replay (~30 min compute, ≤ 4 threads) |
| `code/` | zip_blob_audit.py, dtable_diff.py, w2_cell_check.py, controls_mpmath.py, cmp_chain_all.py |
| `verify.py` | cheap network re-checks (Zenodo metadata, pinned files, exact value); stdlib only |
