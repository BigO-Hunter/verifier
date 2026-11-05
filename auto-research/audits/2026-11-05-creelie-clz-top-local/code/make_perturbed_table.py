"""Negative control: perturb the kernel table, expect the certificate to REJECT.

Zeroes the rigorous lower bounds on cells 4160-4190 and 7940-7960 — the cells
containing the seven r=1 gaps of the F_8 minimizer at mu0=1/3200
(checks/lm8.txt: gaps [1.0461 1.9894 1.9868 1.0419 1.9868 1.9894 1.0461] ->
cells 4184, 7957, 7947, 4167, 7947, 7957, 4184). The r=1 weight is a_1=2/7 and
sum(w) over those gaps is ~1.66e-3, so the drop through the minimizer is ~4.7e-4,
far below T=13/3125=0.00416 (true local min 0.0041773, margin only 1.7e-5):
the run must end FAIL, not VERIFIED. Measured: FAIL box lb=0.004159967975 in 0.5s.

Usage: python3 make_perturbed_table.py [workdir]
  reads  <workdir>/repo/verify/w4000.bin   (default workdir /tmp/clz_rerun)
  writes <workdir>/w4000_perturbed.bin
"""
import os
import struct
import sys

w = sys.argv[1] if len(sys.argv) > 1 else "/tmp/clz_rerun"
src = os.path.join(w, "repo", "verify", "w4000.bin")
dst = os.path.join(w, "w4000_perturbed.bin")
vals = list(struct.unpack("<46000d", open(src, "rb").read()))
print("before: cell 4184 w=%.17g  cell 4168 w=%.17g  cell 7957 w=%.17g  cell 7947 w=%.17g"
      % (vals[4184], vals[4168], vals[7957], vals[7947]))
for i in list(range(4160, 4191)) + list(range(7940, 7961)):
    vals[i] = 0.0
open(dst, "wb").write(struct.pack("<%dd" % len(vals), *vals))
print("zeroed cells 4160-4190 and 7940-7960 ->", dst)
