#!/usr/bin/env python3
"""verify.py — cheap re-checks of the critical-line-zeros v1.3.0 audit (stdlib only; network).

Runs:
 (1) Zenodo 23489033 metadata: version 1.3.0, MIT, file creelie/mh-phys-v1.3.0.zip, size 9,126,044 B,
     md5 f2a3bff3... (the record's own checksum);
 (2) the artifact's sha256 (5afc161e...), fetched from Zenodo and hashed in memory (9 MB download);
 (3) GitHub at pin aff473549: sha256 of verify/w4000.bin, verify/w4000_80k.bin, verify/d4000_80k.bin
     and of verify/weights10.txt == the pins in data/source.json / the README claims; the author's
     verify/bbpcf10.log still reports nodes=1424333714 for the ten-zero certificate;
 (4) the weights file's linear total is exactly 7999/2000000 (Fraction arithmetic);
 (5) the exact claim in 60-digit Decimal (H embedded from the mpmath dps=60 run):
     (125000/124111)(H - 7999/2000000) = 0.67328963959621996..., the claimed 0.6732896395 is its
     10-digit truncation (correct rounding 0.6732896396), and the paper's condition
     11c0 < 0.4794 < (4/3)w(11/20) holds with c0 = 889/125000;
 (6) this package's own MANIFEST.json matches the files on disk (offline integrity of the evidence).

--full prints the pointer to the complete local rerun (evidence/replay.sh: table rebuilds, the
ten-zero certificate twice, eig_lemma, chain_window10, chain_all, the 0.0071125 negative control;
~30 min compute on <=4 threads).

Exit 0 iff every check passes.
"""
import hashlib
import json
import os
import sys
import urllib.request
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 60
HERE = os.path.dirname(os.path.abspath(__file__))

PIN = "aff473549ca8cacf6b6b890cacf67e8d3d458934"
ZIP = "creelie/mh-phys-v1.3.0.zip"
ZIP_SIZE = 9126044
ZIP_MD5 = "f2a3bff3d553b36f7c5647bd71ab92ef"
ZIP_SHA = "5afc161ed79c43e60d5d9d75b713f49125492bf8b10f1dc1d250cc0b13798ac2"
SHAS = {
    "verify/w4000.bin": "8ea9e0208216cb99f4cdcbcaa160b75ba7e7c89058f4d0396392df4f3afa42d5",
    "verify/w4000_80k.bin": "fd9304e375e0e140a3046478dd8d382b6316887e16e10064d1f1ceb42175ea64",
    "verify/d4000_80k.bin": "8915be681c85094d6a8686d078d4de01740fd139f5c7226bf116f6baca14c105",
    "verify/weights10.txt": "PINS",
}
# H = 3/2 - cot(1/sqrt2)/sqrt2, mpmath dps=60
H = Decimal("0.67250070367941164573437979080329518859340302862626")
NODES = "1424333714"

results = []


def check(name, ok, detail=""):
    results.append(bool(ok))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" — {detail}" if detail else ""))


def fetch(url):
    req = urllib.request.Request(url, headers={"User-Agent": "clz-v130-audit/1.0"})
    with urllib.request.urlopen(req, timeout=120) as r:
        return r.read()


def main():
    try:
        rec = json.loads(fetch("https://zenodo.org/api/records/23489033"))
        f0 = rec["files"][0]
        check(
            "zenodo 23489033 metadata (v1.3.0, MIT, file size+md5)",
            rec["metadata"].get("version") == "1.3.0"
            and rec["metadata"].get("license", {}).get("id") == "mit-license"
            and f0["key"] == ZIP
            and f0["size"] == ZIP_SIZE
            and f0["checksum"] == "md5:" + ZIP_MD5,
            f"version={rec['metadata'].get('version')} license={rec['metadata'].get('license', {}).get('id')} "
            f"size={f0['size']} {f0['checksum']}",
        )
    except Exception as e:
        check("zenodo metadata fetch", False, repr(e))

    try:
        blob = fetch("https://zenodo.org/api/records/23489033/files/creelie/mh-phys-v1.3.0.zip/content")
        got_md5 = hashlib.md5(blob).hexdigest()
        got_sha = hashlib.sha256(blob).hexdigest()
        check(
            "artifact md5+sha256+size (fetched from Zenodo, not shipped in this package)",
            len(blob) == ZIP_SIZE and got_md5 == ZIP_MD5 and got_sha == ZIP_SHA,
            f"{len(blob)} B md5={got_md5} sha256={got_sha[:16]}...",
        )
    except Exception as e:
        check("artifact fetch", False, repr(e))

    raw = f"https://raw.githubusercontent.com/creelie/mh-phys/{PIN}/"
    ok_shas, detail = True, []
    for path, want in SHAS.items():
        if want == "PINS":
            continue
        try:
            got = hashlib.sha256(fetch(raw + path)).hexdigest()
            ok_shas = ok_shas and got == want
            detail.append(f"{path}={got[:16]}...")
        except Exception as e:
            ok_shas = False
            detail.append(f"{path}: {e!r}")
    check("pinned tables at aff473549 have the recorded sha256", ok_shas, "; ".join(detail))

    try:
        wtext = fetch(raw + "verify/weights10.txt").decode()
        total = Fraction(0)
        for line in wtext.splitlines():
            p = line.split()
            if p and p[0] == "b":
                total += Fraction(int(p[2]), int(p[3]))
        check("weights10.txt linear total is exactly 7999/2000000", total == Fraction(7999, 2000000), str(total))
    except Exception as e:
        check("weights10.txt fetch", False, repr(e))

    try:
        log = fetch(raw + "verify/bbpcf10.log").decode()
        check(
            "author's verify/bbpcf10.log still reports the audited node count",
            f"nodes={NODES}" in log and "F >= 889/125000" in log,
            f"nodes={NODES}",
        )
    except Exception as e:
        check("author log fetch", False, repr(e))

    mu = Decimal(7999) / 2000000
    c0 = Decimal(889) / 125000
    exact = (H - mu) / (1 - c0)
    closed = (Decimal(125000) / 124111) * (H - mu)
    check("exact bound at 60 digits", str(exact).startswith("0.67328963959621996210"), str(exact)[:32] + "...")
    check("closed form (125000/124111)(H-7999/2000000) equals (H-mu)/(1-c0)", abs(exact - closed) < Decimal("1e-55"))
    check(
        "claimed 0.6732896395 is the 10-dp truncation; 10-dp rounding is 0.6732896396 (claim understates, D2)",
        Decimal(f"{float(exact):.10f}") == Decimal("0.6732896396")
        and Decimal("0.6732896395") < exact < Decimal("0.6732896396"),
        f"exact-claim={exact - Decimal('0.6732896395'):.3e}",
    )
    check("1 - c0 == 124111/125000 exactly", 1 - c0 == Decimal(124111) / 125000, "exact")
    check(
        "paper condition 11*c0 < 0.4794 < (4/3)*w(11/20)",
        11 * c0 < Decimal("0.4794") < (Decimal(4) / 3) * Decimal("0.4794187462372933864263058810"),
        f"11c0={11 * c0:.6f}",
    )

    man_path = os.path.join(HERE, "MANIFEST.json")
    try:
        man = json.load(open(man_path))
        bad, normalized = [], []
        for path, want in man["sha256"].items():
            full = os.path.join(HERE, path)
            raw = open(full, "rb").read() if os.path.exists(full) else None
            got = hashlib.sha256(raw).hexdigest() if raw is not None else None
            if got != want and raw is not None and hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest() == want:
                got, normalized = want, normalized + [path]  # a checkout with core.autocrlf=true
            if got != want:
                bad.append(path)
        check(
            "package MANIFEST.json matches the files in this folder",
            not bad,
            f"{len(man['sha256'])} entries, bad={bad}"
            + (f", {len(normalized)} CRLF-normalized by the checkout" if normalized else ""),
        )
    except Exception as e:
        check("MANIFEST check", False, repr(e))

    if "--full" in sys.argv:
        print(
            "\nFULL rerun (~30 min compute on <=4 threads; requires a rounding-sound compiler — GCC with\n"
            "-frounding-math, NOT Apple clang — and python-flint==0.9.0 numpy scipy):\n"
            "  bash auto-research/audits/2026-11-05-creelie-clz-v130-local/evidence/replay.sh\nThe\n"
            "ten-zero certificate takes ~3 min on four threads; its expected last line is\n"
            "  VERIFIED R=10: F >= 889/125000 with weights verify/weights10.txt; grid=4000 threads=4 nodes=1424333714"
        )
    sys.exit(0 if all(results) else 1)


if __name__ == "__main__":
    main()
