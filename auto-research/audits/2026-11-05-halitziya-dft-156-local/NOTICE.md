This audit replays HalitZiyaKARTAL's pinned Lean formalization of the exact DFT
power-saving bound `π/1000` stated at the reduced fraction
`31415926535897932384626433/10^28` (bigospeedrun/verifier PR #156). The
submission repository `HalitZiyaKARTAL/bigO-dft-verifier` at commit
`da94a2a6f593caa1f534f1ab1c84b88ff5d74906` and the verifier repository are both
Apache-2.0. This package contains only audit code, logs, and digests; it copies
no part of the source proof.

Upstream credits per the submission's own headers (Submission.lean, v6):
Ali Romman (research/balanced-query-tree, CrocSwap/integer-mult-bounds PR #6348)
— the binary query tree caller; Cinna Davis (PR4440, PR4470) — the thin query
and query-thinned path; CubeJerry and the P104 lineage
(research/p104-owned772-relay-descent, commit f714f27d6) — the owned772 P104
word supplier; Jacob Sussman — the Lean engine, the strict tensor power and the
Fourier chain; OpenAI — the exact computational model, the statement and the
all-length reduction (openai/math). Author and supervisor: Halit Ziya KARTAL.
