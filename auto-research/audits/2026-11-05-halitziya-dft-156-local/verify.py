#!/usr/bin/env python3
"""Reproduce the local audit of the DFT submission saving pi/1000 (PR #156).

Clones HalitZiyaKARTAL/bigO-dft-verifier at the pinned SHA, stages the
verifier's own build layout (VerifierChallenge = trusted challenge bytes plus
the generated Race.bound target at the submitted bound, the Submission tree, a
VerifierAudit axiom probe on Race.bound and Race.bound_pi), builds with Lean
4.34.1 / mathlib d13f23b, prints the axiom closures, re-runs the
comment-stripped textual diff of the computational model, and runs the
code/Scope.lean in-kernel probes.

Read-only with respect to the submission repository.

Usage:
  python3 verify.py [--workdir DIR] [--packages-cache DIR] [--verifier-root DIR]

--packages-cache may point at a warm .lake/packages tree for the pinned
mathlib (e.g. a previous audit's stage); without it Lake fetches and builds
mathlib itself (hours).

--verifier-root may point at a bigospeedrun/verifier checkout, whose
challenges/dft/UniformFourier233.lean is the trusted challenge.
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

REPO = 'https://github.com/HalitZiyaKARTAL/bigO-dft-verifier.git'
SHA = 'da94a2a6f593caa1f534f1ab1c84b88ff5d74906'
SUBDIR = 'submissions/dft/halitziyakartal-halitziyav6-pi'
CHALLENGE_REL = 'challenges/dft/UniformFourier233.lean'
CHALLENGE_SHA256 = '3a646acd3ac9cf6ff93e29cc363dbfea0c8953a2e1415f7965bd86e8b2ee62a3'
BOUND = (31415926535897932384626433, 10000000000000000000000000000)
GENERATED_SHA256 = '5a0b655ae2ca9447d9252a91de4114621b1db5df888f8b46d74ee2f3d15546bd'
TOOLCHAIN = 'leanprover/lean4:v4.34.1'
MATHLIB_REV = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
AXIOMS_OK = {'propext', 'Quot.sound', 'Classical.choice'}


def run(args, **kw):
    print('+', ' '.join(map(str, args)), flush=True)
    return subprocess.run([str(a) for a in args], check=True, **kw)


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def blob(repo, rel):
    """The tracked blob's bytes at HEAD, immune to core.autocrlf in the working tree."""
    data = subprocess.check_output(['git', '-C', str(repo), 'cat-file', 'blob', f'HEAD:{rel}'])
    return digest_bytes(data), data


def strip_comments(text):
    """Lean nested block comments and line comments, preserving newlines
    (mirrors the verifier's own strip_comments)."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; out.append('  '); i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2
        elif depth:
            out.append(text[i] if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n':
                i += 1
        else:
            out.append(text[i]); i += 1
    return ''.join(out)


def norm(text):
    return re.sub(r'\s+', ' ', strip_comments(text)).strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workdir', default='audit-dft-156-work')
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
    # is the tracked bytes. The blob-level digest checks below are what
    # actually guard the statement; this only keeps the staged copy faithful.
    run(['git', '-C', clone, '-c', 'core.autocrlf=false',
         'checkout', '--detach', 'FETCH_HEAD'])
    assert subprocess.check_output(['git', '-C', clone, 'rev-parse', 'HEAD'],
                                   text=True).strip() == SHA

    stage = work / 'stage'
    stage.mkdir(parents=True)
    sub = clone / SUBDIR
    shutil.copyfile(sub / 'Submission.lean', stage / 'Submission.lean')
    shutil.copytree(sub / 'Submission', stage / 'Submission')

    # The statement must be the trusted bytes, compared at the tracked-blob
    # level so a core.autocrlf=true working tree cannot mask or fake it
    # (PRs #102/#97's note).
    fork_sha, fork_bytes = blob(clone, CHALLENGE_REL)
    assert fork_sha == CHALLENGE_SHA256, (
        'fork challenge blob does not match the profile-pinned digest')
    trusted_bytes = fork_bytes
    if opt.verifier_root:
        v_sha, v_bytes = blob(opt.verifier_root, CHALLENGE_REL)
        assert v_sha == CHALLENGE_SHA256, (
            'verifier checkout challenge blob does not match the profile-pinned digest')
        trusted_bytes = v_bytes
        assert trusted_bytes == fork_bytes, (
            'tracked challenge differs from the trusted bytes')
    print('tracked challenge is the trusted bytes:', CHALLENGE_SHA256)

    # VerifierChallenge: the trusted challenge plus the verifier's generated
    # Race.bound target at the submitted bound (scripts/submissions.py
    # challenge_source for problem dft, entrypoint Race.bound; the bound is
    # already reduced, so as_integer_ratio leaves n, d unchanged).
    n, d = BOUND
    target = (f'\n-- Big O Speedrun exact-bound target; generated from validated integers.\n'
              f'open OAI.PowerSaving Filter Asymptotics\n\n'
              f'theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧\n'
              f'    (fun n : ℕ => (W n : ℝ)) =O[atTop]\n'
              f'      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - ({n} : ℝ) / {d})) := by\n'
              f'  sorry\n')
    generated = trusted_bytes.decode('utf-8') + target
    gen_sha = digest_bytes(generated.encode())
    assert gen_sha == GENERATED_SHA256, (
        f'regenerated challenge {gen_sha} does not match the challenge_source rerun')
    (stage / 'VerifierChallenge.lean').write_text(generated)
    print('generated challenge sha256:', gen_sha)
    (stage / 'VerifierAudit.lean').write_text(
        'import Submission\n#print axioms Race.bound\n#print axioms Race.bound_pi\n')
    (stage / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
    manifest = json.loads((clone / 'profiles/lake-manifest.json').read_text())
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
        try:
            # APFS clonefile copy: near-instant, read-only source untouched.
            run(['cp', '-cR', opt.packages_cache, stage / '.lake/packages'])
        except Exception:
            shutil.copytree(opt.packages_cache, stage / '.lake/packages')

    # Scope: the RAM model section of the trusted challenge must equal the
    # submission's copy, comment-stripped and whitespace-normalized.
    ch = trusted_bytes.decode('utf-8')
    ram = (stage / 'Submission/OAI/Computability/FourierTransform/RAM.lean').read_text()
    ch_model = re.search(r'namespace PowerSaving.*?end PowerSaving', ch, re.S).group(0)
    s_model = re.search(r'namespace PowerSaving.*?end PowerSaving', ram, re.S).group(0)
    model_ok = norm(ch_model) == norm(s_model)
    print('model section comment-stripped identical:', model_ok,
          f'({len(norm(ch_model))} chars normalized)')

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
    stray = [ln for ln in text.splitlines()
             if "declaration uses `sorry`" in ln and 'VerifierChallenge.lean' not in ln]
    print('sorry warnings outside VerifierChallenge.lean:', len(stray))

    axioms = {}
    for m in re.finditer(r"'(Race\.bound(?:_pi)?)' depends on axioms: \[(.*?)\]", text, re.S):
        axioms[m.group(1)] = {a.strip() for a in m.group(2).split(',')}
    for name in sorted(axioms):
        print(f'{name} axioms:', sorted(axioms[name]))

    probe_ok = True
    print('--- code/Scope.lean ---', flush=True)
    r = subprocess.run(['lake', 'env', 'lean', 'code/Scope.lean'], cwd=stage,
                       capture_output=True, text=True)
    print(r.stdout.strip() or r.stderr.strip())
    probe_ok = r.returncode == 0

    ok = (model_ok and probe_ok and not stray and len(axioms) == 2
          and all(a and a <= AXIOMS_OK for a in axioms.values()))
    print('AUDIT', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
