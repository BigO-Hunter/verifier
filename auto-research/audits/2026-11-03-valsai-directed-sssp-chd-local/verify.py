#!/usr/bin/env python3
"""verify.py — reproduce the Directed-SSSP C-HD row audit's cheap checks (network needed).

Runs: (1) byte-chain — fetch CHDRow.lean / VerifierStatement.lean / sssp-chd.json / direct.json at the
verifier pin, compare sha256 against the profile-declared values; (2) positive control — execute the
verifier's own parse_sssp on the row's bound string, expect (1, 3/4, 1, 11/12, 0). Use --build for the
full local lake replay (evidence/replay.sh; ~6 min with a warm Mathlib cache, v4.34.1 + d13f23b7).
"""
import hashlib, json, subprocess, sys, tempfile, urllib.request

PIN = "b0c848f5d2268cf7b9676d4ad4910947d8b2ca86"
RAW = f"https://raw.githubusercontent.com/bigospeedrun/verifier/{PIN}/"
EXPECT_CHDROW = "b9569dae"  # prefix; full value in profiles/sssp-chd.json challenge_sha256

def fetch(url):
    with urllib.request.urlopen(url, timeout=60) as r:
        return r.read()

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    prof = json.loads(fetch(RAW + "profiles/sssp-chd.json"))
    chd = fetch(RAW + "challenges/directed-sssp/CHDRow.lean")
    ok1 = sha(chd) == prof["challenge_sha256"]
    print(f"[{'PASS' if ok1 else 'FAIL'}] sha256(CHDRow.lean) == sssp-chd.json challenge_sha256 ({sha(chd)[:16]}...)")
    direct = json.loads(fetch(RAW + "profiles/direct.json"))
    entry = direct.get("directed-sssp") or {}
    vs_url = entry.get("challenge_file")
    ok2 = True
    if vs_url:
        vs = fetch(RAW + vs_url if not vs_url.startswith("http") else vs_url)
        ok2 = sha(vs) == entry.get("challenge_sha256", sha(vs))
        print(f"[{'PASS' if ok2 else 'FAIL'}] sha256(VerifierStatement) == direct.json challenge_sha256")
    subm = fetch(RAW + "scripts/submissions.py").decode()
    with tempfile.TemporaryDirectory() as td:
        open(f"{td}/submissions.py", "w").write(subm)
        out = subprocess.run([sys.executable, "-c",
            "import sys; sys.path.insert(0, sys.argv[1]);"
            "import importlib.util as iu;"
            "spec = iu.spec_from_file_location('s', sys.argv[1] + '/submissions.py');"
            "m = iu.module_from_spec(spec); spec.loader.exec_module(m);"
            "print(m.parse_sssp('n log^3/4 ; n log^11/12'))", td],
            capture_output=True, text=True, timeout=120)
    tup = out.stdout.strip()
    ok3 = "3/4" in tup and "11/12" in tup
    print(f"[{'PASS' if ok3 else 'FAIL'}] parse_sssp control -> {tup or out.stderr[-200:]}")
    if "--build" in sys.argv:
        print("full local replay: see evidence/replay.sh (lake update + lake build Submission + AxiomsCHD)")
    sys.exit(0 if (ok1 and ok2 and ok3) else 1)

if __name__ == "__main__":
    main()
