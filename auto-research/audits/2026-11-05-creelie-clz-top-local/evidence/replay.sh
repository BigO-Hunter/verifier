#!/bin/bash
# Full local replay of the critical-line-zeros top-row audit (creelie/mh-phys @ a772d9962).
# Needs: a ROUNDING-SOUND compiler — GCC with -frounding-math (Apple clang ignores FENV_ACCESS;
# this audit used Homebrew gcc-16 on Apple M4 Max arm64, author used x86-64 Linux gcc);
# python-flint==0.9.0 numpy scipy; ~30 min compute at <=4 threads.
# Mirrors the pin's own .github/workflows/verify.yml plus the second certificate and negatives.
set -u
AUDIT="$(cd "$(dirname "$0")/.." && pwd)"   # package root: code/ lives there
W=${1:-/tmp/clz_rerun}
GCC=${GCC:-gcc-16}
mkdir -p "$W" && cd "$W" || exit 9
echo "=== START $(date -u +%FT%TZ) gcc=$($GCC --version | head -1) ==="

/usr/bin/git clone -q https://github.com/creelie/mh-phys repo && cd repo || exit 9
/usr/bin/git -c core.autocrlf=false checkout -qf a772d9962c6e075edbac2008274dba58b0e2980e || exit 9
echo "--- STEP 0: pin identity ---"
/usr/bin/git log -1 --format='%H %ci'

python3 -m venv ../venv && ../venv/bin/pip install -q python-flint==0.9.0 numpy scipy mpmath

echo "--- STEP 1: table rebuild + cmp (CI-identical) ---"
s=$(date +%s); ../venv/bin/python -I verify/table.py 4000 80000 ../w80k_check.bin
cmp ../w80k_check.bin verify/w4000_80k.bin && echo "CMP_80K=IDENTICAL"
cmp <(head -c 368000 ../w80k_check.bin) verify/w4000.bin && echo "CMP_46K_PREFIX=IDENTICAL"
shasum -a 256 verify/w4000.bin  # expect 8ea9e0208216cb99f4cdcbcaa160b75ba7e7c89058f4d0396392df4f3afa42d5
echo "table_elapsed=$(( $(date +%s) - s ))s"

echo "--- STEP 2: compile (author flags) ---"
$GCC -O2 -frounding-math -fopenmp -o ../bbp verify/bbp.c -lm
$GCC -O2 -frounding-math -o ../bb verify/bb.c -lm

echo "--- STEP 3: certificate 1 (board row): F_8 >= 13/3125, mu0=1/3200 ---"
s=$(date +%s); OMP_NUM_THREADS=2 ../bbp 8 4000 verify/w4000.bin 1 3200 13 3125
echo "cert1_rc=$? elapsed=$(( $(date +%s) - s ))s  # expect VERIFIED, nodes=10039560518, checksum=d5746ef8030b2d5c"

echo "--- STEP 4: certificate 2: F_8 >= 605/100000, mu0=1/2000 (serial) ---"
s=$(date +%s); ../bb 8 4000 verify/w4000.bin 1 2000 605 100000
echo "cert2_rc=$? elapsed=$(( $(date +%s) - s ))s  # expect VERIFIED, nodes=5440924378, max_stack=144"

echo "--- STEP 5: eigenvalue lemma + ceiling ---"
../venv/bin/python -I checks/eig_lemma.py | tee ../eig_lemma.rerun.txt
diff ../eig_lemma.rerun.txt checks/eig_lemma.txt && echo "EIG_IDENTICAL"
../venv/bin/python -I checks/chain_all.py > ../chain_all.rerun.txt 2>&1
tail -1 ../chain_all.rerun.txt  # expect: max over all mu: 0.6735602  (<= 0.67357)

echo "--- STEP 6: negative controls (expect FAIL / RC=1 from both) ---"
OMP_NUM_THREADS=2 ../bbp 8 4000 verify/w4000.bin 1 3200 14 3125; echo "neg_T14_rc=$?"
../venv/bin/python "$AUDIT/code/make_perturbed_table.py" "$W"  # zeroes minimizer gap cells -> ../w4000_perturbed.bin
OMP_NUM_THREADS=2 ../bbp 8 4000 "$W/w4000_perturbed.bin" 1 3200 13 3125; echo "neg_table_rc=$?"

echo "--- STEP 7: exact-value controls (50 digits) ---"
../venv/bin/python "$AUDIT/code/controls_mpmath.py"
echo "=== DONE $(date -u +%FT%TZ) ==="
