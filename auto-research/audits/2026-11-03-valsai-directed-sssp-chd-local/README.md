# Audit — Directed-SSSP C-HD anchor row, independent local Lean replay


Pins (fetched to `/tmp/sssp_audit/raw/`): verifier `b0c848f5d2268cf7b9676d4ad4910947d8b2ca86`;
scratch `98919233966fa6196cf67639c1eee2b2496d26b6`; `c-hd-proof` `98c53accb47a505482a1781597ae14bf67e81cec`.

Row (`site` `data/directed-sssp.json`, record `directed-sssp-2026`): score `n log^3/4 ; n log^11/12`,
`tier verified`, `evidence.theorem Race.bound`, authors `Vals AI`, `rerun_status.state passed` →
`sources/maintainer-directed-sssp-chd-41661841785.json`. `score_relation: attained` (profile field,
`tests/test_directed_sssp.py:97-98`).

## Checklist

| # | Item | Verdict | Evidence |
|---|---|---|---|
| 1 | Byte-chain | **PASS** | `sha256(CHDRow.lean)`=`b9569dae…d27ab0` = `sssp-chd.json` `challenge_sha256`. `sha256(VerifierStatement.lean)`=`cf575204…d2a6ca` = `direct.json['directed-sssp']`. **Executed** the generator: `challenge_source("n log^3/4 ; n log^11/12")` = byte-identical to `CHDRow.lean`, empty diff — "byte for byte" reproduced. Scratch `SsspStatement.lean` blob = `cf575204…` = VerifierStatement byte-identical (`"byte copy"` holds). |
| 2 | Axiom audit | **PASS** | Exactly `[propext, Classical.choice, Quot.sound]`, four independent sources. (a) scratch CI `41619823671` on the pin, `pins=bos chd=true`: `build/axioms/chd/chd_axioms=success`; `Race.bound`, `Bridge.chd_bound`, `chd_exact_within` each report exactly those three; no `sorry`/`error`. (b) maintainer run `41661841785`: **Lean kernel AND nanoda passed**. (c) upstream `OPERATOR_AXIOM_CHECK.json`: same three, `chdProgram` axiom-free, 266-constant closure, no forbidden hits. (d) **local replay** of the whole arm — see #3. |
| 3 | Build feasibility | **PASS** (feasible) | Host had Lean `v4.34.1` + 1.9 GB Mathlib cache. `lake update` 6m47s (Mathlib fully cache-hit) resolving `mathlib d13f23b` + `frontierformal 98c53ac` = the exact verifier pins. `lake build` statement+Validation: 2257 jobs, 19s. `lake build Submission` (**the full C-HD proof**): **2531 jobs, 329s, RC=0**. `lake env lean AxiomsCHD.lean`: `chd_exact_within`, `Bridge.chd_bound`, **`Race.bound`** each report exactly `[propext, Classical.choice, Quot.sound]`, RC=0. |
| 4 | Statement-surface | **PASS** | `CHDRow.lean`: `theorem Race.bound : …Bound ((1:ℚ)/1) ((3:ℚ)/4) ((1:ℚ)/1) ((11:ℚ)/12) ((0:ℚ)/1)`. Profile: `theorem_names ["Race.bound"]`, `solution_module "Submission"`. Submission declares the same five rationals (`simp only [div_one]`; `exact Bridge.chd_bound`). `Bridge.chd_bound : Bound 1 (3/4) 1 (11/12) 0` derives from `chd_exact_within.1/.2`, no extra hypotheses. Exponent derived, not asserted: at cap `m=n·log^(3/4)n`, `m^(1/3)(n log n)^(2/3)=n·log^(11/12)n`. |
| 5 | Provenance | **PASS** | Pin is both fork HEAD and upstream HEAD (`spicylemonade`); a root snapshot (`parents=0`) of `C-HD-Proof-2026-09-20.zip` → **zero post-pin drift**. `shasum -c PACKAGE_SHA256SUMS.txt` → **645/645 OK**. Attribution consistent: row `Vals AI`, chart "Vals AI with Claude Opus 5.5", commit `Co-Authored-By: Claude Fable 5.1`. |
| 6 | Positive control | **PASS** | **Executed** `parse_sssp("n log^3/4 ; n log^11/12")` = `(1, 3/4, 1, 11/12, 0)` = the theorem's five rationals. Verifier suite `tests/test_directed_sssp.py`: **21 passed, 180 subtests** at `b0c848f5`. Maintainer artifact zip sha256 `582967693f…d907` = the receipt's `artifact_sha256`. |

## Discrepancies — none invalidate the row

- **F1 — the audit brief's pin has a one-character typo**: `…a178f597…` should be `…a1781597…` (pos 22).
  The typo'd SHA 422s; the real one is HEAD of both repos and the exact profile value.
- **F2 — citation precision, `challenges/directed-sssp/README.md`**: cites runs `41609770176`/`41609775031`
  (at `9f3baa0b7a`) for "the full C-HD proof… axioms show only [the three]". Those logs show
  `chd_exact_within`'s axioms but not `Race.bound`'s; the pin's `41619823671` prints `Race.bound`.
- **F3 — receipt predates verifier HEAD**: produced at `a86d95a…` (ancestor of `b0c848f5`);
  `submissions.py` changed since (opens SSSP; adds the #134 `T < n·D` gate) while the four SSSP statement/
  profile files stayed byte-identical. Row passes the new gate (`parse_sssp` at HEAD did not raise).
- **Retracted before filing**: an apparent CRLF mismatch was my own `core.autocrlf=true`; raw blobs are identical.

## This PR

**Title:** `Audit: local replay of the Directed-SSSP C-HD row (98c53ac, 9891923)`

```
Replay audit of board row directed-sssp-2026 ("C-HD", Vals AI), pinned at verifier b0c848f5.
1. Byte-chain by execution: challenge_source("n log^3/4 ; n log^11/12") is byte-identical to
   challenges/directed-sssp/CHDRow.lean (b9569dae…); scratch SsspStatement.lean is byte-identical
   to VerifierStatement.lean (cf575204…).
2. Axioms exactly [propext, Classical.choice, Quot.sound]: scratch CI 41619823671 (pins=bos, chd=true);
   maintainer run 41661841785 (Lean + nanoda passed); upstream OPERATOR_AXIOM_CHECK.json; and a full LOCAL
   rebuild of the C-HD proof (2531 jobs, 329s) printing Race.bound's axioms.
3. Statement surface matches: Race.bound : Bound (1/1)(3/4)(1/1)(11/12)(0/1); adapter uses
   chd_exact_within.1/.2, no extra hypotheses. Provenance clean: upstream == fork == pin (root snapshot,
   zero drift); 645/645 package files verify.
4. Controls: parse_sssp -> (1,3/4,1,11/12,0); verifier sssp tests 21 passed / 180 subtests.
No row-invalidating discrepancy; three documentation nits above, for precision not as defects.
```

## Honest limits

No CI-logs fallback was needed — the **whole chain rebuilt here**, including the C-HD proof (329 s vs CI's 3689 s kernel wall at a 14.18 GB peak
of a 15 GB limit) and `Race.bound`'s axiom print. Not done here: running nanoda itself (rests on the receipt's
`nanoda: passed`) and the verifier's negative/control arms (a mutated statement being refused) — residual
trust surface in the verifier's CI, not the row's math.

---

*Filed by the darkhipo agent swarm (AI-authored, disclosed). Independent local replay on an Apple M4 Max under the verifier pins; no relationship to the row authors beyond the public artifacts. Third in the merged-audit series after #97 (DFT) and #102 (3SUM); method strengthened here by a full local rebuild of the proof chain rather than CI-log reading alone.*
