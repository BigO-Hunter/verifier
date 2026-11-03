#!/usr/bin/env python3
"""Reproduce the local audit of the 3SUM submission 384055881637/200000000000 (issue #99).

Clones Wang-jiong-han/3sum-weighted-cache at the pinned SHA, stages the
verifier's own build layout (VerifierChallenge with the generated Race.bound
target at the submitted bound, the Submission tree, a VerifierAudit axiom probe),
builds with Lean 4.33.1 / mathlib 0df444a3, prints the axiom closure of
Race.bound, and runs the scope probe and the opaque control arm.

Read-only with respect to the submission repository.

Usage:
  python3 verify.py [--workdir DIR] [--packages-cache DIR] [--verifier-root DIR]

--packages-cache may point at a warm .lake/packages tree for the pinned mathlib
(e.g. a previous audit's stage); without it Lake fetches and builds mathlib
itself (hours).

--verifier-root may point at a bigospeedrun/verifier checkout, whose
challenges/3sum-apsp/EndStatement.lean is the trusted challenge. Without it the
script uses the submission's own Submission/EndStatement.lean after refusing to
continue unless its sha256 equals the profile-pinned digest below.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

REPO = 'https://github.com/Wang-jiong-han/3sum-weighted-cache.git'
SHA = 'e1ae71db2231f172c6541820e2ce0a54aa14fc64'
CHALLENGE_REL = 'Submission/EndStatement.lean'
CHALLENGE_SHA256 = '4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987'
BOUND = (384055881637, 200000000000)
TOOLCHAIN = 'leanprover/lean4:v4.33.1'
MATHLIB_REV = '0df444a360eaa60ab8c11dca51a86af692955474'
AXIOMS_OK = {'propext', 'Quot.sound', 'Classical.choice'}


def run(args, **kw):
    print('+', ' '.join(map(str, args)), flush=True)
    return subprocess.run([str(a) for a in args], check=True, **kw)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def blob(repo, rel):
    """The tracked blob's bytes at HEAD, immune to core.autocrlf in the working tree."""
    data = subprocess.check_output(['git', '-C', str(repo), 'cat-file', 'blob', f'HEAD:{rel}'])
    return hashlib.sha256(data).hexdigest(), data


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workdir', default='audit-3sum-99-work')
    ap.add_argument('--packages-cache', default=None)
    ap.add_argument('--verifier-root', default=None)
    opt = ap.parse_args()
    work = Path(opt.workdir).resolve()
    if work.exists():
        sys.exit(f'{work} exists; remove it first')
    clone = work / 'clone'
    run(['git', 'init', clone])
    run(['git', '-C', clone, 'fetch', '--depth=1', REPO, SHA])
    # core.autocrlf=false matches the Linux verifier runner, so the staged tree
    # is the tracked bytes. The blob-level digest check below is what actually
    # guards the statement; this only keeps the staged copy faithful.
    run(['git', '-C', clone, '-c', 'core.autocrlf=false',
         'checkout', '--detach', 'FETCH_HEAD'])
    assert subprocess.check_output(['git', '-C', clone, 'rev-parse', 'HEAD'],
                                   text=True).strip() == SHA

    stage = work / 'stage'
    stage.mkdir(parents=True)
    shutil.copyfile(clone / 'Submission.lean', stage / 'Submission.lean')
    shutil.copytree(clone / 'Submission', stage / 'Submission')

    # The statement module must be the trusted bytes, not a normalized copy.
    # Compare the tracked blob, so a core.autocrlf=true working tree (which
    # rewrites the checkout to CRLF) cannot mask or fake the comparison.
    blob_sha, blob_bytes = blob(clone, CHALLENGE_REL)
    assert blob_sha == CHALLENGE_SHA256, (
        'tracked statement module does not match the profile-pinned challenge digest')
    trusted_bytes = blob_bytes
    if opt.verifier_root:
        # Compare the tracked BLOB, not the working tree: a core.autocrlf=true
        # checkout rewrites the same LF blob to CRLF bytes (PR #102's note).
        v_sha, v_bytes = blob(opt.verifier_root, 'challenges/3sum-apsp/EndStatement.lean')
        assert v_sha == CHALLENGE_SHA256, (
            'verifier checkout challenge blob does not match the profile-pinned digest')
        trusted_bytes = v_bytes
        assert trusted_bytes == blob_bytes, (
            'tracked statement module differs from the trusted bytes')
    print('tracked statement module is the trusted bytes:', CHALLENGE_SHA256)

    # VerifierChallenge: the trusted challenge plus the verifier's generated
    # Race.bound target (scripts/submissions.py challenge_source for problem
    # 3sum, entrypoint Race.bound). The bound is already reduced, so
    # Fraction(bound).as_integer_ratio() leaves n, d unchanged.
    n, d = BOUND
    target = (f'\n-- Big O Speedrun exact-bound target; generated from validated integers.\n'
              f'theorem Race.bound : EndStatement.ThreeSum.SolvedInTime (({n} : Rat) / {d}) := by\n'
              f'  sorry\n')
    generated = trusted_bytes.decode('utf-8') + target
    (stage / 'VerifierChallenge.lean').write_text(generated)
    print('generated challenge sha256:',
          hashlib.sha256(generated.encode()).hexdigest())
    (stage / 'VerifierAudit.lean').write_text('import Submission\n#print axioms Race.bound\n')
    (stage / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
    # The submission's own manifest pins the same mathlib revision as
    # profiles/anthropic-lake-manifest.json; refuse to build on any other pin.
    manifest = json.loads((clone / 'lake-manifest.json').read_text())
    rev = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
    assert rev == MATHLIB_REV, f'mathlib pin {rev} does not match the profile'
    (stage / 'lake-manifest.json').write_text(json.dumps(manifest))
    (stage / 'lakefile.toml').write_text(f'''name = "Verifier"
version = "0.1.0"
[leanOptions]
autoImplicit = false
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "{MATHLIB_REV}"

[[lean_lib]]
name = "Submission"

[[lean_lib]]
name = "VerifierChallenge"

[[lean_lib]]
name = "VerifierAudit"
''')
    (stage / '.lake/build').mkdir(parents=True)
    if opt.packages_cache:
        shutil.copytree(opt.packages_cache, stage / '.lake/packages')

    # Probes travel with this package; they are compiled against the staged build.
    here = Path(__file__).resolve().parent
    shutil.copytree(here / 'code', stage / 'code')

    t0 = time.time()
    log = work / 'local-build.log'
    with log.open('w') as f:
        run(['lake', 'build', 'VerifierAudit', 'VerifierChallenge'], cwd=stage,
            stdout=f, stderr=subprocess.STDOUT)
    print(f'lake build exit 0 in {time.time() - t0:.0f}s')

    text = log.read_text()
    m = re.search(r"warning: VerifierChallenge.lean:\d+:\d+: declaration uses `sorry`", text)
    print('only expected sorry is the generated target:', bool(m))
    stray = [ln for ln in text.splitlines()
             if "declaration uses `sorry`" in ln and 'VerifierChallenge.lean' not in ln]
    print('sorry warnings outside the generated target:', len(stray))

    m = re.search(r"'Race\.bound' depends on axioms: \[(.*?)\]", text, re.S)
    axioms = {a.strip() for a in m.group(1).split(',')} if m else set()
    print('Race.bound axioms:', sorted(axioms))

    # Scope probe and opaque control arm, compiled with the staged environment.
    probe_ok = True
    control_saw_sorry = False
    for probe in ('code/Scope.lean', 'code/OpaqueControl.lean'):
        print(f'--- {probe} ---', flush=True)
        r = subprocess.run(['lake', 'env', 'lean', probe], cwd=stage,
                           capture_output=True, text=True)
        print(r.stdout.strip() or r.stderr.strip())
        probe_ok = probe_ok and r.returncode == 0
        if probe.endswith('OpaqueControl.lean'):
            control_saw_sorry = 'sorryAx' in r.stdout

    ok = (axioms <= AXIOMS_OK and bool(axioms) and probe_ok
          and control_saw_sorry and not stray)
    print('AUDIT', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
