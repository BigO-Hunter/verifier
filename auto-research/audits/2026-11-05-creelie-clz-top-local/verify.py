#!/usr/bin/env python3
"""verify.py — cheap re-checks of the critical-line-zeros top-row audit (stdlib only; network for Zenodo/GitHub).

Runs:
 (1) Zenodo 23480715 metadata: license MIT, file key/size/md5 of creelie/mh-phys-v1.0.0.zip;
 (2) local artifact copy evidence/maintainer-artifact.zip: md5 + sha256 (offline byte provenance);
 (3) GitHub at pin a772d9962: verify/w4000.bin sha256 == README claim 8ea9e020...afa42d5;
 (4) successor disclosure: Zenodo 23489033 (v1.3.0) md5 f2a3bff3... and the 0.6732896395 claim;
 (5) exact row value in stdlib Decimal (50 digits, H embedded from the mpmath dps=60 run):
     (3125/3112)(H - 7/3200) = 0.67311335523719839104..., board display 0.6731134 = exact + 4.476e-8
     (7-dp rounding), and ordering ours > Jo > H.
 --full prints the pointer to the complete local rerun (evidence/replay.sh: table rebuild +
 both branch-and-bound certificates + eig_lemma + chain_all + negative controls; ~30 min compute).
Exit 0 iff every check passes.
"""
import hashlib
import json
import os
import sys
import urllib.request
from decimal import Decimal, getcontext

getcontext().prec = 60

HERE = os.path.dirname(os.path.abspath(__file__))
PIN = "a772d9962c6e075edbac2008274dba58b0e2980e"
ZIP_MD5 = "8a575fece758bda2f21eb4455a67d2a1"
ZIP_SHA = "34d1a3bf6643b6ff7a91f697acb5185b988c37189b2f37d4264c1b8968b1a693"
TABLE_SHA = "8ea9e0208216cb99f4cdcbcaa160b75ba7e7c89058f4d0396392df4f3afa42d5"
SUCC_MD5 = "md5:f2a3bff3d553b36f7c5647bd71ab92ef"
# H = 3/2 - cot(1/sqrt2)/sqrt2, mpmath dps=60 (evidence/controls_mpmath.log)
H = Decimal("0.67250070367941164573437979080329518859340302862626")

results = []


def check(name, ok, detail=""):
    results.append(ok)
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" — {detail}" if detail else ""))


def fetch(url):
    with urllib.request.urlopen(url, timeout=60) as r:
        return r.read()


def main():
    try:
        rec = json.loads(fetch("https://zenodo.org/api/records/23480715"))
        f0 = rec["files"][0]
        check(
            "zenodo 23480715 metadata",
            rec["metadata"]["license"]["id"] == "mit-license"
            and f0["key"] == "creelie/mh-phys-v1.0.0.zip"
            and f0["size"] == 5822744
            and f0["checksum"] == "md5:" + ZIP_MD5,
            f"license={rec['metadata']['license']['id']} file={f0['key']} md5={f0['checksum']}",
        )
        succ = json.loads(fetch("https://zenodo.org/api/records/23489033"))
        sf = succ["files"][0]
        check(
            "successor 23489033 (v1.3.0, stale-row disclosure)",
            sf["checksum"] == SUCC_MD5 and "67.32" in succ["metadata"]["title"],
            f"md5={sf['checksum']} title~{succ['metadata']['title'][:60]}",
        )
    except Exception as e:  # network optional-degrade: report, count as failure
        check("zenodo metadata fetch", False, repr(e))

    zpath = os.path.join(HERE, "evidence", "maintainer-artifact.zip")
    if os.path.exists(zpath):
        blob = open(zpath, "rb").read()
        check(
            "local artifact md5+sha256",
            hashlib.md5(blob).hexdigest() == ZIP_MD5 and hashlib.sha256(blob).hexdigest() == ZIP_SHA,
            f"{len(blob)} bytes",
        )
    else:
        check("local artifact present", False, zpath)

    try:
        tab = fetch(f"https://raw.githubusercontent.com/creelie/mh-phys/{PIN}/verify/w4000.bin")
        check(
            "w4000.bin at git pin == README sha256 claim",
            hashlib.sha256(tab).hexdigest() == TABLE_SHA,
            f"{len(tab)} bytes sha256={hashlib.sha256(tab).hexdigest()[:16]}...",
        )
    except Exception as e:
        check("github pin fetch", False, repr(e))

    exact = (Decimal(3125) / 3112) * (H - Decimal(7) / 3200)
    s = str(exact)
    jo = (Decimal(1345000) * H - 2680) / 1340003
    delta = Decimal("0.6731134") - exact
    check(
        "exact row value (Decimal, 50 digits)",
        s.startswith("0.67311335523719839104"),
        s[:32] + "...",
    )
    check(
        "board display = 7-dp rounding of exact (+4.476e-8, NOT an error)",
        Decimal(f"{float(exact):.7f}") == Decimal("0.6731134")
        and Decimal("4.476e-8") < delta < Decimal("4.477e-8"),
        f"delta={delta:.6e}",
    )
    check("ordering ours > Jo > H", exact > jo > H, f"ours-Jo={exact - jo:.6e}")

    if "--full" in sys.argv:
        print(
            "\nFULL rerun (table rebuild + both certificates + eig_lemma + chain_all + negative\n"
            "controls, ~30 min compute on 4 threads): see evidence/replay.sh — requires a\n"
            "rounding-sound compiler (GCC with -frounding-math; NOT Apple clang) and\n"
            "python-flint==0.9.0 numpy scipy."
        )
    sys.exit(0 if all(results) else 1)


if __name__ == "__main__":
    main()
