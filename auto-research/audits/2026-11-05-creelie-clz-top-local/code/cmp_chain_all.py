"""Rotation-aware comparison of chain_all rerun vs shipped checks/chain_all.txt.
Pattern tuples are cyclic words: L-BFGS-B may converge to a rotation. Every other
field (gbar, E, bound lines, max) must match exactly."""
import re

def canon(pat):
    nums = tuple(pat)
    if len(set(nums)) == 1:  # constant word: period is not identifiable, collapse
        return (nums[0],)
    return min(nums[i:] + nums[:i] for i in range(len(nums)))

def parse(path):
    rows = []
    for ln in open(path):
        ln = ln.rstrip("\n")
        m = re.match(r"mu=([\d.]+): pattern=\(([^)]*)\) gbar=([\d.]+) E<=([\d.]+)", ln)
        if m:
            pat = tuple(float(x) for x in m.group(2).split(",") if x.strip())
            rows.append(("pat", m.group(1), canon(pat), m.group(3), m.group(4)))
            continue
        m = re.match(r"mu in \[([\d.,]+)\]: bound<=([\d.]+) with pattern \(([^)]*)\)", ln)
        if m:
            pat = tuple(float(x) for x in m.group(3).split(",") if x.strip())
            rows.append(("bnd", m.group(1), canon(pat), m.group(2)))
            continue
        m = re.match(r"max over all mu: ([\d.]+)", ln)
        if m:
            rows.append(("max", m.group(1)))
    return rows

a = parse("/tmp/clz_zenodo_audit/exec/chain_all_rerun.txt")
b = parse("/tmp/clz_zenodo_audit/exec/mh-phys/checks/chain_all.txt")
print("rows rerun/shipped:", len(a), len(b))
assert len(a) == len(b)
bad = 0
for x, y in zip(a, b):
    if x != y:
        print("DIFF:", x, "vs", y)
        bad += 1
print("non-rotation differences:", bad)
mx = [r for r in a if r[0] == "max"]
print("max line:", mx)
assert bad == 0 and mx == [("max", "0.6735602")]
assert float(mx[0][1]) <= 0.67357
print("CHAIN_ALL: identical up to cyclic rotation; ceiling 0.6735602 <= 0.67357 PASS")
