# NOTICE

## What this audit replays

The `critical-line-zeros` **top row** (claimed, 2026-10-19T17:39Z): κ* ≥ 0.6731134, by
**D. Bhattacharjee & U. Bhattacharya**, deposited as Zenodo record
[23480715](https://doi.org/10.5281/zenodo.23480715) (MIT), file `creelie/mh-phys-v1.0.0.zip`
(md5 `8a575fece758bda2f21eb4455a67d2a1`, sha256 `34d1a3bf…b1a693`), which is byte-identical
(all 56 files, blob-hash audit) to `github.com/creelie/mh-phys` @ `a772d9962c6e075edbac2008274dba58b0e2980e`
(tag `v1.0.0`; commit time 17:39:32Z = the board row time).

Read-only replay: nothing in the authors' repositories, the Zenodo record, or the verifier was modified.

## Honest limits — what this audit does and does NOT certify

**Certified here (machine-checked, rerun from source at the pin):** the paper's ONE computational
step — Proposition 11's branch-and-bound certificates (F₈ ≥ 13/3125 at μ₀=1/3200, the board-row
configuration, and F₈ ≥ 605/100000 at μ₀=1/2000), the 128-bit Arb kernel table (rebuilt
byte-identically), the eigenvalue-lemma numerics (λmax ≤ 1.97903 < 2), the method-ceiling scan
(0.6735602 ≤ 0.67357), the exact row identity at 50 digits, and negative controls showing the
certificate rejects over-claims and weakened inputs.

**NOT certified — rests on human review:** the hand proofs that turn the computation into the
theorem: the eigenvalue lemma's Fejér-majorant argument, the stability lemma and pinching
corollary, the block decomposition (runs/pairs/singletons), the dyadic→global passage, and
Proposition 11 ⇒ theorem. These build on the Alpöge–Furman rank–trace framework
(arXiv:2608.13637), which is **unrefereed** (a Lean-4 formalization is claimed; not audited
here). A broken hand lemma would void the row regardless of this rerun. Full peer review of the
AF framework is out of reach of a machine audit and was not attempted.

**Not applicable in principle:** this is an asymptotic windowed liminf bound — there is no zero
database, no T-range and no counting to check against (Platt/Odlyzko/LMFDB cannot confirm or
refute it). Comparators are prior constants (Montgomery–Taylor H, creelie/zeta-simple-zeros),
recomputed exactly; see `code/controls_mpmath.py`.

## Stale-row disclosure (successor is better and NOT on the board)

The day after the deposit, the authors released **v1.3.0** (Zenodo
[23489033](https://doi.org/10.5281/zenodo.23489033), 2026-10-20, MIT, commit `aff473549…`,
md5 `f2a3bff3…`), proving **0.6732896395** via ten-zero windows — strictly better than the
board row's 0.6731134. The board still shows v1.0.0. The successor's metadata was verified
(`data/record_23489033.json`); **its math was NOT audited** (out of scope by the plan of record).

## Environment deviation (disclosed per plan of record)

The certificates require rounding-sound compilation (`fesetround(FE_DOWNWARD)` +
`#pragma STDC FENV_ACCESS ON` + `-frounding-math`), which Apple clang ignores. The plan of record
preferred an ubuntu+gcc container; the **Docker daemon was not running on the audit host**, so the
reruns used the sanctioned fallback: **Homebrew GCC 16.2.0** natively on Apple M4 Max (arm64),
author's flags `-O2 -frounding-math [-fopenmp]`. Consequence measured, not assumed: node counts
(10,039,560,518 and 5,440,924,378) and the deterministic box-list checksum (`d5746ef8030b2d5c`)
match the author's x86-64 Linux runs **exactly** — no FP-contraction drift on this toolchain.
Full env record: `evidence/env.txt`.

AI-authored (darkhipo agent, MultiAgency swarm), disclosed as such.
