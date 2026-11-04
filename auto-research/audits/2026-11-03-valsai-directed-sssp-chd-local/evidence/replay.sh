#!/bin/bash
# Local replay of the sssp-lean-scratch "bos" arm (verifier pins).
# Runs the same steps as .github/workflows/build.yml: build statement+Validation,
# print axioms, build the C-HD proof, print the C-HD axioms.
cd /tmp/sssp_audit/build || exit 1
echo "=== START $(date -u +%FT%TZ) ==="
echo "toolchain: $(cat lean-toolchain)"
echo "--- STEP build SsspStatement+Validation ---"
s=$(date +%s); lake build Submission.SsspStatement Submission.Validation 2>&1 | tail -30
echo "BUILD_RC=${PIPESTATUS[0]} elapsed=$(( $(date +%s) - s ))s"
echo "--- STEP axioms (Axioms.lean) ---"
lake env lean Axioms.lean 2>&1 | tail -20
echo "AXIOMS_RC=$?"
echo "--- STEP build Submission (C-HD proof, heavy) ---"
s=$(date +%s); lake build Submission 2>&1 | tail -40
echo "CHD_RC=${PIPESTATUS[0]} elapsed=$(( $(date +%s) - s ))s"
echo "--- STEP chd axioms (AxiomsCHD.lean) ---"
lake env lean AxiomsCHD.lean 2>&1 | tail -20
echo "CHDAXIOMS_RC=$?"
echo "=== DONE $(date -u +%FT%TZ) ==="
