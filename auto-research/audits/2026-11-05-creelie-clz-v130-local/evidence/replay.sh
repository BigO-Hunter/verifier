#!/bin/bash
# Full local replay of the critical-line-zeros v1.3.0 audit (R2125608601).
#
# Requirements: a rounding-sound compiler (Homebrew GCC 16; Apple clang IGNORES -frounding-math and
# would make the branch-and-bound unsound), python-flint==0.9.0, numpy, scipy, mpmath.
# Expected wall time ~30 min on 4 threads; the ten-zero certificate alone is ~3 min.
#
# Inputs: a clone of github.com/creelie/mh-phys at aff473549ca8cacf6b6b890cacf67e8d3d458934
# (verified byte-identical to the Zenodo 23489033 zip: see code/zip_blob_audit.py). The deposited
# zip is deliberately NOT shipped in this package; fetch it from Zenodo and hash-check it first:
#   curl -L -o mh-phys-v1.3.0.zip \
#     https://zenodo.org/api/records/23489033/files/creelie/mh-phys-v1.3.0.zip/content
#   md5sum mh-phys-v1.3.0.zip   # f2a3bff3d553b36f7c5647bd71ab92ef
#   sha256sum mh-phys-v1.3.0.zip  # 5afc161ed79c43e60d5d9d75b713f49125492bf8b10f1dc1d250cc0b13798ac2
#   unzip mh-phys-v1.3.0.zip && cd creelie-mh-phys-aff4735
#
# Usage: bash replay.sh /path/to/mh-phys          (a git clone at the pin)
set -euo pipefail
REPO="${1:?usage: replay.sh /path/to/mh-phys-clone-at-aff4735}"
GCC="${GCC:-gcc-16}"
WORK="$(mktemp -d)"
export OMP_NUM_THREADS="${OMP_NUM_THREADS:-4}"
cd "$WORK"

echo "== 0. pins =="
git -C "$REPO" rev-parse HEAD | grep -q '^aff473549ca8cacf6b6b890cacf67e8d3d458934$' \
  || { echo "repo is not at the pinned commit"; exit 1; }
sha256sum "$REPO"/verify/w4000.bin "$REPO"/verify/w4000_80k.bin "$REPO"/verify/d4000_80k.bin

echo "== 1. kernel table rebuild (expect byte-identical) =="
python3 -I "$REPO"/verify/table.py 4000 80000 w80k_check.bin
cmp w80k_check.bin "$REPO"/verify/w4000_80k.bin && echo "CMP_80K=IDENTICAL"
python3 -I "$REPO"/verify/table.py 4000 46000 w4000_check.bin
cmp w4000_check.bin "$REPO"/verify/w4000.bin && echo "CMP_46K=IDENTICAL"

echo "== 2. second-order table rebuild (expect 6-cell platform deviation, D1) =="
python3 -I "$REPO"/verify/dtable.py 4000 80000 4 d80k_check.bin
python3 -I "$REPO"/verify/dtable.py 4000 80000 4 d80k_check2.bin   # determinism
cmp d80k_check.bin d80k_check2.bin && echo "REBUILD_DETERMINISTIC"
cmp d80k_check.bin "$REPO"/verify/d4000_80k.bin && echo "CMP_DTABLE=IDENTICAL" \
  || echo "CMP_DTABLE=DIFFERS (record the magnitude; see code/dtable_diff.py)"
python3 code/w2_cell_check.py "$REPO" d80k_check.bin || true

echo "== 3. ten-zero certificate with the SHIPPED tables (expect VERIFIED, nodes=1424333714) =="
"$GCC" -O2 -frounding-math -fopenmp -o bbp_cf "$REPO"/verify/bbp_cf.c -lm
./bbp_cf 10 4000 "$REPO"/verify/w4000_80k.bin "$REPO"/verify/d4000_80k.bin \
  "$REPO"/verify/weights10.txt 889 125000 | grep -v '^progress' | tee run10.log
grep -q '^VERIFIED R=10: F >= 889/125000' run10.log

echo "== 4. ten-zero certificate with the PLATFORM-REBUILT second-order table (expect same nodes) =="
./bbp_cf 10 4000 "$REPO"/verify/w4000_80k.bin d80k_check.bin \
  "$REPO"/verify/weights10.txt 889 125000 | grep -v '^progress' | tee run10_rebuilt.log
grep -q 'nodes=1424333714' run10_rebuilt.log

echo "== 5. negative control: the author's over-claim T=0.0071125 must FAIL =="
if ./bbp_cf 10 4000 "$REPO"/verify/w4000_80k.bin "$REPO"/verify/d4000_80k.bin \
  "$REPO"/verify/weights10.txt 71125 10000000 | grep -v '^progress' | tee neg.log; then
  echo "UNEXPECTED: the over-claim verified"; exit 1
else
  grep -q '^FAIL box' neg.log && echo "OVER-CLAIM REJECTED (expected)"
fi

echo "== 6. eigenvalue lemma (expect digit-for-digit identical output) =="
python3 -I "$REPO"/checks/eig_lemma.py | tee eig_lemma.log
diff <(sed 's/[[:space:]]*$//' eig_lemma.log) <(sed 's/[[:space:]]*$//' "$REPO"/checks/eig_lemma.txt) \
  && echo "EIG_IDENTICAL"

echo "== 7. ten-zero weight ceiling (expect max 0.6732908 at mu=0.004) =="
python3 -I "$REPO"/checks/chain_window.py 4 0.0015,0.002,0.0025,0.003,0.0035,0.004,0.005 9 | tee chain_window10.log
grep -q 'mu=0.004 m=9:0.6732908' chain_window10.log

echo "== 8. method ceiling (expect max 0.6735602; ~4 min) =="
python3 -I "$REPO"/checks/chain_all.py | tee chain_all.log
grep -q '^max over all mu: 0.6735602' chain_all.log

echo "== 9. exact arithmetic (60 digits) =="
python3 code/controls_mpmath.py "$REPO"/verify/weights10.txt

echo "ALL REPLAY STEPS DONE — compare logs with evidence/ in this package"
