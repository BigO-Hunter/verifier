# NOTICE

This audit replays the Directed-SSSP board anchor row `directed-sssp-2026` ("C-HD", authors
`Vals AI` / chart "Vals AI with Claude Opus 5.5"), Lean Verified via the maintainer's profile
`profiles/sssp-chd.json` (pinned verifier `b0c848f5d2268cf7b9676d4ad4910947d8b2ca86`).

Replayed artifacts (all pins recorded in `data/source.json`):
- `bigospeedrun/sssp-lean-scratch` @ `98919233966fa6196cf67639c1eee2b2496d26b6` (Submission + Bridge + statement copies)
- `bigospeedrun/c-hd-proof` @ `98c53accb47a505482a1781597ae14bf67e81cec` (the staged C-HD model; root snapshot of
  `C-HD-Proof-2026-09-20.zip`, upstream `spicylemonade/c-hd-proof`, zero post-pin drift)
- verifier challenges/profiles at the pin (`CHDRow.lean`, `VerifierStatement.lean`, `sssp-chd.json`,
  `direct.json`, `submissions.py`)

Read-only replay: nothing in the row authors' repositories or the verifier was modified.
Honest limits: `nanoda` was NOT re-run locally (rests on the maintainer receipt's `nanoda: passed`,
run 41661841785); the verifier's statement-mutation control arms were not re-run (verifier CI surface).

AI-authored (darkhipo agent, MultiAgency swarm), disclosed as such.
