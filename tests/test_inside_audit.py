"""Regression test for issue #188: the audit phase must reach execve.

Before the fix, `scripts/inside.py` built `args` for phase == 'audit' but never
assigned `threads`, so the shared `os.execve(..., LEAN_NUM_THREADS=threads)`
raised NameError before Lean ever launched. The audit phase is the only phase
that reuses the final execve without passing through the `else` branch's
`threads = '4'` default.

This test drives the real entrypoint in a subprocess against a stub Lake, so it
catches any NameError/Name-binding regression without a Lean install.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'


class InsideAuditTests(unittest.TestCase):
    def setUp(self):
        self.work = Path(tempfile.mkdtemp(prefix='inside-audit-test-'))
        (self.work / 'control').mkdir()
        (self.work / 'control' / 'request.json').write_text(json.dumps(
            {'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'}}))
        # Stub Lake records argv and LEAN_NUM_THREADS instead of running Lean.
        lake = self.work / 'tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lake'
        lake.parent.mkdir(parents=True)
        lake.write_text('#!/bin/sh\n'
                        'echo "ARGS: $@"\n'
                        'echo "THREADS: $LEAN_NUM_THREADS"\n')
        lake.chmod(0o755)

    def tearDown(self):
        import shutil
        shutil.rmtree(self.work, ignore_errors=True)

    def run_phase(self, phase):
        return subprocess.run(
            [sys.executable, str(SCRIPTS / 'inside.py'), str(self.work), phase],
            capture_output=True, text=True)

    def test_audit_phase_launches_lean_with_thread_default(self):
        # Issue #188: this raised NameError: name 'threads' is not defined.
        r = self.run_phase('audit')
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn('ARGS: env lean', r.stdout)
        self.assertIn('stage/VerifierAudit.lean', r.stdout)
        self.assertIn('THREADS: 4', r.stdout)

    def test_other_phases_keep_their_thread_defaults(self):
        # The non-build path must keep the same default the audit phase gets.
        r = self.run_phase('lean')
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn('ARGS: env', r.stdout)
        self.assertIn('THREADS: 4', r.stdout)


if __name__ == '__main__':
    unittest.main()
