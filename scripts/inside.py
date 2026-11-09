#!/usr/bin/python3
"""Trusted entrypoint, executed only inside the outer offline namespace."""
import json
import os
from pathlib import Path
import sys

work = Path(sys.argv[1])
phase = sys.argv[2]
request = json.loads((work / 'control/request.json').read_text())
stage = work / 'stage'
lean = work / 'tools/elan/toolchains' / request['request']['lean_toolchain'].replace('/', '--').replace(':', '---') / 'bin/lake'
if phase.endswith('-exec'):
    # `lake env` prepends its toolchain bin to PATH. Restore the reviewed
    # adapter only after Lake has supplied LEAN_PATH and other package paths.
    kernel = phase.removesuffix('-exec')
    if kernel not in ['lean', 'nanoda']:
        raise ValueError('invalid kernel phase')
    env = dict(os.environ, LEAN_NUM_THREADS='4')
    env['PATH'] = str(work / 'control/bin') + ':' + env['PATH']
    comparator = work / 'tools/comparator/.lake/build/bin/comparator'
    os.execve(str(comparator), [str(comparator), str(work / f'control/{kernel}.json')], env)
# Non-build phases (audit, lean/nanoda exec) run with a fixed thread count;
# only the build phase takes the controller's Lake worker count.
threads = '4'
if phase == 'audit':
    args = [str(lean), 'env', 'lean', str(stage / 'VerifierAudit.lean')]
else:
    # Submission code can write build products. Never trust its copy of the
    # challenge .olean/trace on a later run. Removal itself stays sandboxed,
    # so hostile output symlinks cannot reach the host checkout or receipts.
    for facet in ['lib/lean', 'ir']:
        parent = stage / '.lake/build' / facet
        if parent.exists():
            for path in parent.glob('VerifierChallenge.*'):
                if path.is_dir() and not path.is_symlink():
                    raise RuntimeError('unexpected challenge output directory')
                path.unlink()
    if phase == 'build':
        # Split job 1: one parallel build with the real Lake, not the chain shim. Lake's
        # LEAN_NUM_THREADS sets how many modules build at once (verifier.py LAKE_WORKERS).
        threads = sys.argv[3] if len(sys.argv) == 4 else ''
        if threads not in ['1', '2', '3', '4']:
            raise ValueError('invalid Lake worker count')
        args = [str(lean), 'build', request['profile']['solution_module']]
    else:
        args = [str(lean), 'env', '/usr/bin/python3', str(work / 'control/inside.py'),
                str(work), phase + '-exec']
os.execve(str(lean), args, dict(os.environ, LEAN_NUM_THREADS=threads))
