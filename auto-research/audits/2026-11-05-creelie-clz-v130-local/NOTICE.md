# NOTICE

## What this audit replays

The `critical-line-zeros` **successor release v1.3.0** (published 2026-10-20T03:35Z), claimed
κ* ≥ 0.6732896395 by **D. Bhattacharjee & U. Bhattacharya**, deposited as Zenodo record
[23489033](https://doi.org/10.5281/zenodo.23489033) (MIT), file `creelie/mh-phys-v1.3.0.zip`
(9,126,044 B, md5 `f2a3bff3d553b36f7c5647bd71ab92ef`, sha256 `5afc161ed79c43e60d5d9d75b713f49125492bf8b10f1dc1d250cc0b13798ac2`),
which is byte-identical (all 84 files, blob-hash audit) to `github.com/creelie/mh-phys` @
`aff473549ca8cacf6b6b890cacf67e8d3d458934` (tag `v1.3.0`, ls-remote verified; commit time
2026-10-20T03:34:49Z, 23 s before the Zenodo record was created).

Read-only replay: nothing in the authors' repositories, the Zenodo record, or the verifier was
modified.

## Predecessor

This package is the follow-up of
[`../2026-11-05-creelie-clz-top-local/`](../2026-11-05-creelie-clz-top-local/) (audit of release
v1.0.0, Zenodo 23480715, bound 0.6731133552), which disclosed this successor as
"metadata verified, math NOT audited". This package audits that successor's math. Where the two
packages overlap (the shipped `verify/bbp.c`/`bb.c` uniform-weight certificates of release 1.0.0,
`checks/eig_lemma.py`, `checks/chain_all.py`), the earlier audit's reruns remain the record; this
package re-ran `eig_lemma` and `chain_all` against the v1.3.0 tree as well, and reports them.

## Honest limits — what this audit does and does NOT certify

**Certified here (machine-checked, rerun from source at the pin):** the claim's ONE new
computational step — the ten-zero window inequality F₁₀ ≥ 889/125000 for the weights of Table I
(μ = 7999/2000000), by branch and bound with the cell bound and the second-order Taylor bound in
128-bit ball arithmetic; the kernel table (rebuilt byte-identically) and the second-order tables
(rebuilt, with the six-cell platform deviation D1 measured and shown immaterial); the
eigenvalue-lemma numerics (λmax ≤ 1.97903 < 2); the ten-zero weight ceiling (0.6732908); the
method-ceiling scan (0.6735602 ≤ 0.67357); the exact arithmetic of `(H−μ)/(1−c₀)` at 60 digits,
the weights file's linear total, and the paper's condition `11c₀ < 0.4794 < (4/3)w(11/20)`; and a
negative control (the author's own over-claim T = 0.0071125 is rejected at a single cell).

**NOT certified — rests on human review:** the hand proofs that turn the computation into the
theorem: the eigenvalue lemma's Fejér-majorant argument, the stability lemma and pinching
corollary, the block decomposition (runs/pairs/singletons), the dyadic→global passage, and
Proposition 11 ⇒ theorem. In particular this package verifies the *algebra* `(H−μ)/(1−c₀) =
(125000/124111)(H−7999/2000000)` but does **not** verify the block-decomposition lemma that
produces `(H−μ)/(1−c₀)` from the per-window inequality. These build on the Alpöge–Furman
rank–trace framework (arXiv:2608.13637), which is **unrefereed** (a Lean-4 formalization is
claimed; not audited here). A broken hand lemma would void the claim regardless of this rerun.

**Not applicable in principle:** this is an asymptotic windowed liminf bound — there is no zero
database, no T-range and no counting to check against (Platt/Odlyzko/LMFDB cannot confirm or
refute it). Comparators are prior constants (Montgomery–Taylor H, creelie/zeta-simple-zeros),
recomputed exactly; see `code/controls_mpmath.py`.

**Scope of the certificate rerun:** the ten-zero certificate is the claim's load-bearing computer
step. The artifact's weighted nine-zero and eight-zero certificates (releases 1.2.0/1.1.0,
0.6732134/0.6731986) were **not** re-run; they do not support the 0.6732896395 value.

## Row status disclosure (successor is better and NOT on the board)

At this audit's board snapshot (`data/board_row_snapshot.json`, `chat-knowledge.json` fetched
2026-11-05T21:41Z) the row `/other/critical-line-zeros` still lists release **v1.0.0**
(Zenodo 23480715, κ* ≥ 0.673113, evidence Claimed), and record **23489033** appears nowhere in the
site's knowledge JSON. v1.3.0's 0.6732896395 is strictly better than the listed 0.6731134. This
audit does not list it; listing is the maintainers' decision.

## Environment deviation (disclosed)

The certificates require rounding-sound compilation (`fesetround(FE_DOWNWARD)` +
`#pragma STDC FENV_ACCESS ON` + `-frounding-math`), which Apple clang ignores. The reruns used
**Homebrew GCC 16.2.0** natively on Apple M4 Max (arm64), author's flags
`-O2 -frounding-math -fopenmp`, 4 threads. Consequence measured, not assumed: the ten-zero
certificate's node count (1,424,333,714), work-box count (207,518) and deterministic box-list
checksum (`bb2e8f8af3a7efd2`) match the author's Linux run **exactly**, and the box
decomposition (cutoff cells and components per gap) is identical line for line. The kernel table
rebuilds byte-identically; the second-order table rebuild deviates in six 1e-18 cell bounds (D1 in
README), which does not change the certificate. Full env record: `evidence/env.txt`.

## Credits and licence

The audited work is by Deep Bhattacharjee and Ushashi Bhattacharya (MIT licence; see the Zenodo
record). The method builds on the Alpöge–Furman rank–trace framework, on Sunghyeon Jo's
`creelie/zeta-simple-zeros`, and on the Montgomery–Taylor constant; the paper credits Anaxia
(creelie/eBLLM, Zenodo 23484395) for the route. This audit package is released under the same MIT
terms as the audited artifact and contributes no new mathematics.

AI-assisted: this audit was authored by an AI agent (**deepseek-flash**, MultiAgency body harness)
under human direction, with arithmetic and claims verified by the recorded commands; it is
disclosed as such and should be read as a machine check, not as peer review.
