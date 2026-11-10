"""Chained stages (docs/execution.md): the tools hand-over (rules T1 and T2), the Lean receipt
merge of chained job 3, the chain provenance in the receipt, and the nanoda skip rules."""
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import verifier as v


class ToolsAllowListTests(unittest.TestCase):
    def test_allowed_paths(self):
        for rel, is_dir in [('tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean', False),
                            ('tools/elan/bin/elan', False), ('tools/comparator/.lake/build/bin/comparator', False),
                            ('tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export', False),
                            ('tools/nanoda/target/release/nanoda_bin', False), ('tools/landrun/landrun', False),
                            ('tools/elan', True),
                            ('cache/packages/mathlib/.lake/build/lib/lean/Mathlib/Order/Basic.olean', False),
                            ('cache/packages/mathlib', True), ('cache/packages/mathlib/lakefile.lean', True),
                            ('control/inside.py', False), ('control/bin/lake', False)]:
            with self.subTest(rel=rel):
                self.assertTrue(v.tools_allowed(rel, is_dir))

    def test_refused_paths(self):
        for rel, is_dir in [('tools/elan/downloads/elan.tar.gz', False), ('tools/elan/downloads', True),
                            ('tools/elan/tmp/x', False), ('tools/elan/tmp', True),
                            ('Submission.olean', False), ('stage/lib/lean/Submission.olean', False),
                            ('cache/lakefile.toml', False), ('cache/packages', True), ('cache', True),
                            ('cache/.lake/packages/mathlib.olean', False),
                            ('control/request.json', False), ('control/chains.json', False),
                            ('control/lake-workers.txt', False), ('control/lean.json', False),
                            ('control/bin/lake/extra', False), ('receipt.json', False),
                            ('tools/', False), ('tools//lean', False), ('tools/./lean', False),
                            ('../tools/lean', False), ('/tools/lean', False), ('tools/\udcff', False),
                            ('tools/a\0b', False), ('', False), ('control/Inside.py', False),
                            ('control/inside.py.bak', False)]:
            with self.subTest(rel=rel, is_dir=is_dir):
                self.assertFalse(v.tools_allowed(rel, is_dir))

    def test_binaries_name_the_pinned_executables(self):
        rel = v.tool_binaries('leanprover/lean4:v4.34.1')
        self.assertEqual(sorted(rel), ['comparator', 'lake_shim', 'landrun', 'lean', 'lean4export', 'nanoda'])
        self.assertEqual(rel['lean'], 'tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean')


class Base(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        self.tmp = Path(tmp.name)
        self.work, self.art, self.out = self.tmp / 'bos-verifier', self.tmp / 'artifacts', self.tmp / 'tools-artifact'
        for target, value in [('WORK', self.work), ('ART', self.art), ('TOOLS_ARTIFACT', self.out)]:
            patcher = patch.object(v, target, value); patcher.start(); self.addCleanup(patcher.stop)
        (self.work / 'control').mkdir(parents=True); (self.work / 'tools').mkdir()
        v.write_json(self.work / 'control/request.json',
                     {'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'}, 'profile': {}, 'names': ['Race.bound']})
        self.art.mkdir()
        v.save({'started_unix': 1000.0, 'steps': [], 'request': {'repo_url': 'u', 'commit': 'c' * 40},
                'theorem_names': ['Race.bound'], 'verifier_commit': 'd' * 40,
                'kernels': {'lean': {'status': 'not_started'}, 'nanoda': {'status': 'not_started'}}})
        self.output = self.tmp / 'github-output'
        env = patch.dict(os.environ, GITHUB_OUTPUT=str(self.output)); env.start(); self.addCleanup(env.stop)
        self.toolchain = self.work / 'tools/elan/toolchains/leanprover--lean4---v4.34.1'
        self.toolchain.mkdir(parents=True)
        (self.toolchain / 'bin').mkdir()
        (self.toolchain / 'bin/lean').write_bytes(b'LEAN')
        (self.toolchain / 'bin/lake').write_bytes(b'LAKE')

    def build_tools(self):
        """A small but complete trusted-setup layout: one file under each allowed prefix."""
        packages = self.work / 'cache/.lake/packages/mathlib/.lake/build/lib/lean'
        packages.mkdir(parents=True)
        (packages / 'Mathlib.olean').write_bytes(b'MATHLIB')
        (self.work / 'tools/comparator/.lake/build/bin').mkdir(parents=True)
        (self.work / 'tools/comparator/.lake/build/bin/comparator').write_bytes(b'COMPARATOR')
        (self.work / 'tools/nanoda/target/release').mkdir(parents=True)
        (self.work / 'tools/nanoda/target/release/nanoda_bin').write_bytes(b'NANODA')
        (self.work / 'tools/landrun').mkdir()
        (self.work / 'tools/landrun/landrun').write_bytes(b'LANDRUN')
        exporter = self.work / 'tools/comparator/.lake/packages/lean4export/.lake/build/bin'
        exporter.mkdir(parents=True)
        (exporter / 'lean4export').write_bytes(b'EXPORT')
        (self.work / 'control/bin').mkdir()
        (self.work / 'control/bin/lake').write_bytes(b'SHIM')
        (self.work / 'control/inside.py').write_bytes(b'INSIDE')

    def pack_tools(self):
        v.pack_tools()
        return v.receipt()['pack_tools']

    def unpack_tools(self, sha=None, result='success'):
        sha = sha if sha is not None else hashlib.sha256((self.out / 'tools.tar').read_bytes()).hexdigest()

        def command(args, label, *a, **k):
            (self.art / (label + '.log')).write_text('out')
        with patch.dict(os.environ, BOS_TOOLS_RESULT=result, BOS_TOOLS_SHA256=sha), \
             patch.object(v, 'command', side_effect=command):
            v.unpack_tools()

    def tree(self):
        found = {}
        for top, dirs, files in os.walk(self.work / 'tools'):
            for name in dirs + files:
                path = Path(top) / name
                found['tools/' + str(path.relative_to(self.work / 'tools'))] = (
                    path.is_dir(), path.read_bytes() if path.is_file() else None)
        return found


class PackToolsTests(Base):
    def test_pack_keeps_only_the_allow_list(self):
        self.build_tools()
        (self.work / 'tools/elan/downloads/elan.tar.gz').parent.mkdir(parents=True)
        (self.work / 'tools/elan/downloads/elan.tar.gz').write_bytes(b'archive')
        (self.work / 'cache/lakefile.toml').write_bytes(b'config')  # Not under cache/packages.
        (self.work / 'control/extra.json').write_text('{}')  # Control data never travels.
        record = self.pack_tools()
        with tarfile.open(self.out / 'tools.tar') as tar:
            names = [m.name for m in tar.getmembers()]
        self.assertIn('tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean', names)
        self.assertIn('cache/packages/mathlib/.lake/build/lib/lean/Mathlib.olean', names)
        self.assertIn('control/bin/lake', names)
        self.assertIn('control/inside.py', names)
        self.assertNotIn('tools/elan/downloads/elan.tar.gz', names)
        self.assertNotIn('cache/lakefile.toml', names)
        self.assertNotIn('control/extra.json', names)
        # The denied toolchain archive folder is pruned whole; anything outside a walked base
        # (cache/lakefile.toml, control/extra.json) is simply never seen.
        self.assertEqual(record['skipped_count'], 1)
        self.assertEqual(record['skipped_first'], ['tools/elan/downloads'])
        self.assertEqual(record['files'], len(names))
        sha = hashlib.sha256((self.out / 'tools.tar').read_bytes()).hexdigest()
        self.assertEqual(record['sha256'], sha)
        self.assertEqual(self.output.read_text(), 'tools_sha256=' + sha + '\n')
        pins = json.loads((self.out / 'tool-sha256.json').read_text())
        self.assertEqual(sorted(pins), ['comparator', 'lake_shim', 'landrun', 'lean', 'lean4export', 'nanoda'])
        self.assertEqual(pins['lean'], hashlib.sha256(b'LEAN').hexdigest())

    def test_pack_is_deterministic(self):
        self.build_tools()
        first = self.pack_tools()['sha256']
        self.assertEqual(self.pack_tools()['sha256'], first)
        (self.work / 'tools/landrun/landrun').write_bytes(b'CHANGED')
        self.assertNotEqual(self.pack_tools()['sha256'], first)

    def test_pack_needs_the_pinned_layout(self):
        self.build_tools()
        (self.work / 'tools/nanoda/target/release/nanoda_bin').unlink()
        with self.assertRaises(RuntimeError):
            self.pack_tools()
        self.assertFalse((self.out / 'tools.tar').exists())

    def test_pack_refuses_symlinks_and_the_caps(self):
        self.build_tools()
        os.symlink(self.tmp, self.work / 'tools/landrun/Link')
        record = self.pack_tools()
        self.assertIn('tools/landrun/Link', record['skipped_first'])
        v.pack_tools()  # A symlinked directory is pruned, so the second run agrees.
        self.assertEqual(v.receipt()['pack_tools']['sha256'], record['sha256'])
        for name, value in [('TOOLS_MAX_MEMBERS', 2), ('TOOLS_MAX_BYTES', 4)]:
            with self.subTest(cap=name), patch.object(v, name, value), self.assertRaises(RuntimeError):
                self.pack_tools()


class UnpackToolsTests(Base):
    def packed(self):
        self.build_tools()
        self.pack_tools()
        before = self.tree()
        shutil.rmtree(self.work / 'tools'); (self.work / 'tools').mkdir()
        shutil.rmtree(self.work / 'cache', ignore_errors=True)
        (self.work / 'control/bin/lake').unlink(); (self.work / 'control/inside.py').unlink()
        return before

    def test_round_trip_restores_files_and_verifies_the_binaries(self):
        before = self.packed()
        self.unpack_tools()
        after = self.tree()
        self.assertEqual({k: c for k, (_, c) in after.items()}, {k: c for k, (_, c) in before.items()})
        self.assertEqual(after['tools/comparator/.lake/build/bin/comparator'][1], b'COMPARATOR')
        self.assertEqual((self.work / 'control/bin/lake').read_bytes(), b'SHIM')
        self.assertEqual((self.work / 'cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').read_bytes(), b'MATHLIB')
        self.assertEqual(json.loads((self.art / 'tool-sha256.json').read_text())['nanoda'],
                         hashlib.sha256(b'NANODA').hexdigest())
        data = v.receipt()
        self.assertEqual(data['unpack_tools']['files'], data['pack_tools']['files'])
        self.assertEqual(data['unpack_tools']['sha256'], data['pack_tools']['sha256'])
        self.assertFalse((self.out / 'tools.tar').exists())

    def test_fail_closed_before_any_write(self):
        self.packed()
        sha = hashlib.sha256((self.out / 'tools.tar').read_bytes()).hexdigest()
        for kwargs in [dict(result='failure'), dict(result=''), dict(sha=''), dict(sha=sha.upper()),
                       dict(sha=sha[:63]), dict(sha='0' * 64)]:
            with self.subTest(**kwargs), self.assertRaises((RuntimeError, ValueError)):
                self.unpack_tools(**{'sha': sha, **kwargs})
            self.assertEqual(os.listdir(self.work / 'tools'), [])
            self.assertFalse((self.art / 'tool-sha256.json').exists())
        (self.out / 'tools.tar').unlink()
        with self.assertRaises(ValueError):
            self.unpack_tools(sha=sha)
        self.assertEqual(os.listdir(self.work / 'tools'), [])

    def test_a_pinned_binary_that_does_not_match_is_refused(self):
        self.packed()
        pins = json.loads((self.out / 'tool-sha256.json').read_text())
        pins['comparator'] = '0' * 64
        v.write_json(self.out / 'tool-sha256.json', pins)
        with self.assertRaises(ValueError):
            self.unpack_tools()
        self.assertNotIn('unpack_tools', v.receipt())

    def test_missing_or_tampered_pin_file_is_refused(self):
        self.packed()
        pins = json.loads((self.out / 'tool-sha256.json').read_text())
        del pins['landrun']
        v.write_json(self.out / 'tool-sha256.json', pins)
        with self.assertRaises(ValueError):
            self.unpack_tools()
        v.write_json(self.out / 'tool-sha256.json', dict(pins, landrun='nothex'))
        with self.assertRaises(ValueError):
            self.unpack_tools()

    def test_a_bad_member_rejects_the_whole_archive(self):
        self.build_tools()
        self.pack_tools()
        with tarfile.open(self.out / 'tools.tar') as tar:
            good = [(m, tar.extractfile(m).read() if m.isreg() else None) for m in tar.getmembers()]
        os.remove(self.out / 'tools.tar')
        link = tarfile.TarInfo('tools/comparator/evil'); link.type = tarfile.SYMTYPE; link.linkname = '/etc/passwd'
        bad = {'control': tarfile.TarInfo('control/request.json'),
               'download': tarfile.TarInfo('tools/elan/downloads/x.tar.gz'),
               'symlink': link, 'dir-as-file': None}
        bad['dir-as-file'] = tarfile.TarInfo('tools/elan'); bad['dir-as-file'].type = tarfile.DIRTYPE
        for name, member in bad.items():
            with self.subTest(member=name):
                shutil.rmtree(self.work / 'tools'); (self.work / 'tools').mkdir()
                shutil.rmtree(self.work / 'cache', ignore_errors=True)
                (self.work / 'control/bin/lake').unlink(missing_ok=True); (self.work / 'control/inside.py').unlink(missing_ok=True)
                with tarfile.open(self.out / 'tools.tar', 'w', format=tarfile.PAX_FORMAT) as tar:
                    for info, data in good:
                        info.pax_headers.setdefault('mtime', '1.000000000')
                        tar.addfile(info, io.BytesIO(data) if data is not None else None)
                    member.pax_headers.setdefault('mtime', '1.000000000')
                    tar.addfile(member, io.BytesIO(b'x') if member.isreg() else None)
                with self.assertRaises((ValueError, tarfile.TarError)):
                    self.unpack_tools()
                self.assertEqual(os.listdir(self.work / 'tools'), [])
                self.assertNotIn('unpack_tools', v.receipt())

    def test_the_restore_targets_must_be_empty(self):
        self.packed()
        (self.work / 'control/inside.py').write_text('stale')
        with self.assertRaises(RuntimeError):
            self.unpack_tools()
        (self.work / 'control/inside.py').unlink()
        (self.work / 'tools/stale').write_text('stale')
        with self.assertRaises(RuntimeError):
            self.unpack_tools()


LEAN_KERNEL = {'status': 'passed', 'reason': 'comparator_acceptance', 'exit_code': 0, 'wall_seconds': 1.0}
LEAN_ARTIFACT_FILES = {'gate.json': {'status': 'proceed'}, 'selected-request.json': {'issue_number': 42},
                       'lean.log': 'log', 'tool-sha256.json': {'lean': 'x'}}


class MergeBase(Base):
    def setUp(self):
        super().setUp()
        self.lean_dir = self.tmp / 'lean-artifact'
        self.lean_dir.mkdir()
        env = patch.dict(os.environ, GITHUB_RUN_ID='123', GITHUB_RUN_ATTEMPT='1', ISSUE_NUMBER='42',
                         BOS_BUILD_SHA256='a' * 64, BOS_TOOLS_SHA256='b' * 64,
                         BOS_LEAN_ARTIFACT=str(self.lean_dir))
        env.start(); self.addCleanup(env.stop)

    def write_lean_receipt(self, **overrides):
        lean = {'schema_version': 1, 'status': 'not_verified', 'verification_stage': 'lean',
                'started_unix': 2000.0, 'verifier_commit': 'd' * 40, 'run_url': 'https://github.com/o/r/actions/runs/123',
                'steps': [{'name': 'verify_lean', 'exit_code': 0, 'wall_seconds': 1.0}],
                'request': {'repo_url': 'u', 'commit': 'c' * 40}, 'theorem_names': ['Race.bound'],
                'kernels': {'lean': LEAN_KERNEL, 'nanoda': {'status': 'pending', 'reason': 'advisory_queued'}},
                'axiom_audit': {'status': 'passed', 'reported_axioms': {'Race.bound': ['propext']}},
                'build': {'exit_code': 0, 'attempts': []}, 'pack': {'sha256': 'p' * 64},
                'unpack': {'sha256': 'p' * 64}, 'unpack_tools': {'sha256': 'b' * 64},
                'tool_pins': {'nanoda': 'n' * 40}, 'lake_workers': 2,
                'chain_started_unix': 1500.0, 'artifact_sha256': {'lean.log': 'q' * 64}}
        lean.update(overrides)
        v.write_json(self.lean_dir / 'receipt.json', lean)
        for name, content in LEAN_ARTIFACT_FILES.items():
            (self.lean_dir / name).write_text(json.dumps(content) if not isinstance(content, str) else content)
        return lean

    def merged(self):
        v.merge_lean()
        return v.receipt()


class MergeLeanTests(MergeBase):
    def test_the_merge_carries_the_lean_evidence_and_the_chain(self):
        self.write_lean_receipt()
        data = self.merged()
        self.assertEqual(data['kernels']['lean'], LEAN_KERNEL)
        self.assertEqual(data['axiom_audit']['reported_axioms'], {'Race.bound': ['propext']})
        self.assertEqual(data['tool_pins']['nanoda'], 'n' * 40)
        self.assertEqual(data['build'], {'exit_code': 0, 'attempts': []})
        self.assertEqual(data['lake_workers'], 2)
        self.assertEqual(data['chain_started_unix'], 1500.0)
        self.assertEqual(data['stages']['lean']['receipt_sha256'],
                         hashlib.sha256((self.lean_dir / 'receipt.json').read_bytes()).hexdigest())
        self.assertEqual([link['job'] for link in data['chain']['jobs']], ['build', 'lean', 'nanoda'])
        self.assertEqual(data['chain']['jobs'][0]['artifacts']['build']['sha256'], 'a' * 64)
        self.assertEqual(data['chain']['jobs'][0]['artifacts']['tools']['sha256'], 'b' * 64)
        self.assertEqual(data['chain']['started_unix'], 1500.0)
        # Job 2's artifact files reach the final artifact, but this job keeps its own receipt.
        self.assertTrue((self.art / 'gate.json').is_file())
        self.assertTrue((self.art / 'lean.log').is_file())
        self.assertFalse((self.art / 'receipt.json').samefile(self.lean_dir / 'receipt.json'))

    def test_a_receipt_from_another_request_or_commit_is_refused(self):
        self.write_lean_receipt()
        for field, value in [('request', {'repo_url': 'other', 'commit': 'c' * 40}),
                             ('theorem_names', ['Other.bound']), ('verifier_commit', 'e' * 40)]:
            with self.subTest(field=field):
                self.write_lean_receipt(**{field: value})
                with self.assertRaises(ValueError):
                    self.merged()
        self.write_lean_receipt()

    def test_only_a_lean_stage_receipt_merges(self):
        for overrides in [{'verification_stage': 'final'}, {'verification_stage': 'lean', 'kernels': {
                'lean': LEAN_KERNEL, 'nanoda': {'status': 'passed'}}}, {'verification_stage': None}]:
            with self.subTest(overrides=overrides):
                self.write_lean_receipt(**overrides)
                with self.assertRaises(ValueError):
                    self.merged()
        self.write_lean_receipt()

    def test_a_missing_oversized_or_symlinked_receipt_is_refused(self):
        with self.assertRaises(ValueError):
            self.merged()
        self.write_lean_receipt()
        (self.lean_dir / 'receipt.json').write_bytes(b'x' * (2 * 1024**2 + 1))
        with self.assertRaises(ValueError):
            self.merged()
        (self.lean_dir / 'receipt.json').unlink()
        os.symlink(self.art / 'receipt.json', self.lean_dir / 'receipt.json')
        with self.assertRaises(ValueError):
            self.merged()

    def test_oversized_lean_files_do_not_reach_the_final_artifact(self):
        self.write_lean_receipt()
        (self.lean_dir / 'lean.log').write_bytes(b'x' * (32 * 1024**2 + 1))
        self.merged()
        self.assertFalse((self.art / 'lean.log').exists())
        self.assertTrue((self.art / 'gate.json').exists())


class ChainNanodaTests(MergeBase):
    def run_nanoda(self):
        ran = []
        with patch.dict(os.environ, BOS_CHAIN='true'), patch.object(v, 'verify', side_effect=lambda kernels: ran.extend(kernels)):
            v.verify_nanoda()
        return ran

    def test_no_nanoda_run_without_a_lean_result(self):
        v.write_json(self.work / 'control/request.json',
                     {'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'}, 'profile': {}, 'names': ['Race.bound']})
        self.write_lean_receipt(kernels={'lean': {'status': 'not_started'}, 'nanoda': {'status': 'pending', 'reason': 'advisory_queued'}})
        self.merged()
        self.assertEqual(self.run_nanoda(), [])
        data = v.receipt()
        self.assertEqual(data['kernels']['nanoda'], {'status': 'not_started', 'reason': 'lean_check_did_not_run'})
        self.assertEqual(data['status'], 'not_verified')

    def test_no_nanoda_run_after_a_lean_resource_stop(self):
        self.write_lean_receipt(kernels={'lean': dict(LEAN_KERNEL, systemd_result='oom-kill', status='not_completed_or_rejected'),
                                         'nanoda': {'status': 'pending', 'reason': 'advisory_queued'}})
        self.merged()
        self.assertEqual(self.run_nanoda(), [])
        data = v.receipt()
        self.assertEqual(data['kernels']['nanoda'], {'status': 'not_started', 'reason': 'lean_resource_stop'})

    def test_nanoda_runs_after_a_lean_rejection_like_the_single_job_loop(self):
        self.write_lean_receipt(kernels={'lean': dict(LEAN_KERNEL, status='rejected', reason='lean_kernel_rejection'),
                                         'nanoda': {'status': 'pending', 'reason': 'advisory_queued'}})
        self.merged()
        self.assertEqual(self.run_nanoda(), ['nanoda'])

    def test_without_the_chain_flag_the_single_job_semantics_hold(self):
        self.write_lean_receipt(kernels={'lean': {'status': 'not_started'}, 'nanoda': {'status': 'pending', 'reason': 'advisory_queued'}})
        self.merged()
        ran = []
        with patch.dict(os.environ, BOS_CHAIN='', clear=False), patch.object(v, 'verify', side_effect=lambda kernels: ran.extend(kernels)):
            v.verify_nanoda()
        self.assertEqual(ran, ['nanoda'])


if __name__ == '__main__':
    unittest.main()
