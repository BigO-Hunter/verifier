"""Van der Waerden numbers: the closed maintainer profile for OpenAI's own solution (Lead, 2026-11-06, task 55f01df6).
OpenAI's lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean at 1581d4cb, byte for byte, with one target,
OAI.QuantitativeVanDerWaerden.uniform_lower_bound (W_r(k) > k^{k floor(log2 r)/100000}), on our default pins (Lean v4.34.1,
Mathlib d13f23b7), which are also theirs. Closed: only a maintainer dispatch of verify.yml runs it."""
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import verifier as v

PROFILE = json.loads((v.ROOT / 'profiles/van-der-waerden.json').read_text())
PROVENANCE = json.loads((v.ROOT / 'challenges/van-der-waerden/provenance.json').read_text())
FOLDER = v.ROOT / 'challenges/van-der-waerden'
TARGET = 'OAI.QuantitativeVanDerWaerden.uniform_lower_bound'
REQUEST = {'repo_url': 'https://github.com/openai/math',
           'commit': '1581d4cbdd69a0faf34b2089614fe2a814316a6a',
           'challenge_file': 'challenges/van-der-waerden/Challenge.lean',
           'theorem_names': TARGET,
           'lean_toolchain': 'leanprover/lean4:v4.34.1'}


def git_blob(path):
    data = path.read_bytes()
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


class FrozenFilesTests(unittest.TestCase):
    def test_challenge_and_license_are_the_upstream_bytes(self):
        challenge = v.ROOT / PROFILE['challenge_file']
        self.assertEqual(v.digest(challenge), PROFILE['challenge_sha256'])
        self.assertEqual(v.digest(challenge), PROVENANCE['sha256'])
        self.assertEqual(git_blob(challenge), PROVENANCE['git_blob'])
        self.assertEqual(git_blob(FOLDER / 'LICENSE'), PROVENANCE['license_git_blob'])
        self.assertEqual(PROVENANCE['source_commit'], PROFILE['upstream_commit'])
        self.assertEqual(PROVENANCE['source_commit'], REQUEST['commit'])

    def test_the_target_is_the_uniform_bound_at_one_over_100000(self):
        text = (v.ROOT / PROFILE['challenge_file']).read_text()
        self.assertIn('theorem uniform_lower_bound :\n    ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,\n'
                      '      (k : ℝ) ^ ((1 / 100000 : ℝ) * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by\n  sorry', text)
        self.assertIn('noncomputable def W (r k : ℕ) : ℕ :=\n  sInf {N : ℕ | 0 < N ∧ IsRamsey (Fin r) k N}', text)
        self.assertIn('def MonoAP {α : Type u} (c : ℕ → α) (k a d : ℕ) : Prop :=\n  ∀ j < k, c (a + j * d) = c a', text)
        self.assertIn('def HasMonoAP {α : Type u} (c : ℕ → α) (k N : ℕ) : Prop :=\n'
                      '  ∃ a d, 0 < d ∧ a + (k - 1) * d < N ∧ MonoAP c k a d', text)
        # One theorem, no structure (Comparator #68 needs a structure), Mathlib only.
        self.assertEqual(text.count('theorem '), 1)
        self.assertNotIn('structure ', text)
        self.assertEqual([line for line in text.splitlines() if line.startswith('import')], ['import Mathlib'])
        self.assertEqual(PROFILE['theorem_names'], [TARGET])
        self.assertEqual(set(PROFILE['permitted_axioms']), set(v.AXIOMS))
        self.assertEqual(PROFILE['bound'], '1/100000')

    def test_default_pins_and_tools(self):
        self.assertEqual(PROFILE['lean_toolchain'], 'leanprover/lean4:v4.34.1')
        self.assertEqual(PROFILE['manifest_file'], 'profiles/lake-manifest.json')
        self.assertEqual(PROFILE['tools_file'], 'profiles/tools.json')
        revs = {p['name']: p['rev'] for p in json.loads((v.ROOT / PROFILE['manifest_file']).read_text())['packages']}
        self.assertEqual(revs['mathlib'], PROVENANCE['mathlib'])
        self.assertNotIn('solution_dependencies', PROFILE)
        self.assertNotIn('auto_implicit', PROFILE)


class RequestTests(unittest.TestCase):
    def test_the_maintainer_request_selects_this_profile(self):
        profile, names = v.validate_request(dict(REQUEST))
        self.assertEqual(profile, PROFILE)
        self.assertEqual(names, [TARGET])

    def test_other_toolchains_and_names_are_refused(self):
        for toolchain in ['leanprover/lean4:v4.33.1', 'leanprover/lean4:v4.35.0']:
            with self.assertRaisesRegex(ValueError, 'toolchain'):
                v.validate_request(dict(REQUEST, lean_toolchain=toolchain))
        # The other theorems of their Main.lean are not targets.
        for name in ['OAI.QuantitativeVanDerWaerden.uniform_lower_bound_floor',
                     'OAI.QuantitativeVanDerWaerden.exists_uniform_lower_bound', 'Race.bound']:
            with self.assertRaisesRegex(ValueError, 'theorem_names'):
                v.validate_request(dict(REQUEST, theorem_names=name))

    def test_closed_to_issues_and_prs(self):
        self.assertNotIn('van-der-waerden', json.loads((v.ROOT / 'profiles/direct.json').read_text()))


class PrepareTests(unittest.TestCase):
    def test_only_their_progression_coloring_folder_stages(self):
        files = {'README.md': 'outside the folder',
                 'lean/OAI.lean': 'theorem untrusted : False := sorry\n',
                 'lean/OAI/Analysis/Other.lean': 'theorem untrusted : False := sorry\n',
                 'lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean': 'theorem untrusted : False := sorry\n',
                 'lean/OAI/Combinatorics/ProgressionColoring/Main.lean':
                     'import OAI.Combinatorics.ProgressionColoring.Model\n',
                 'lean/OAI/Combinatorics/ProgressionColoring/Model.lean': 'import Mathlib\n',
                 'lean/lakefile.lean': 'untrusted build file', 'lean/lake-manifest.json': '{}',
                 'lean/patches/x.patch': 'untrusted'}
        def clone(url, sha, dest, label, **kwargs):
            self.assertEqual((url, sha, label), (REQUEST['repo_url'], REQUEST['commit'], 'submission'))
            self.assertEqual(kwargs, {'sparse_paths': ['/lean/OAI/Combinatorics/ProgressionColoring/']})
            for name, data in files.items():
                p = dest / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(data)
        def tree(args, **kwargs):
            root = Path(args[2])
            return b''.join(f'100644 blob {"a"*40}\t{p.relative_to(root)}\0'.encode()
                            for p in root.rglob('*') if p.is_file())
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); event = root / 'event.json'; event.write_text(json.dumps({'inputs': REQUEST}))
            with patch.object(v, 'ART', root / 'artifacts'), patch.object(v, 'WORK', root / 'work'), \
                 patch.object(v, 'command'), patch.object(v, 'clone', side_effect=clone), \
                 patch.object(v.subprocess, 'check_output', side_effect=tree), \
                 patch.dict(os.environ, GITHUB_EVENT_PATH=str(event), BOS_REQUEST_PATH=str(event), BOS_SPLIT=''):
                v.prepare()
                hashes = json.loads((root / 'artifacts/source-sha256.json').read_text())
                self.assertEqual(set(hashes), {'OAI/Combinatorics/ProgressionColoring/Main.lean',
                                               'OAI/Combinatorics/ProgressionColoring/Model.lean'})
                stage = root / 'work/stage'
                self.assertEqual((stage / 'VerifierChallenge.lean').read_bytes(), (v.ROOT / PROFILE['challenge_file']).read_bytes())
                self.assertEqual((stage / 'lean-toolchain').read_text(), 'leanprover/lean4:v4.34.1\n')
                control = json.loads((root / 'work/control/lean.json').read_text())
                self.assertEqual((control['challenge_module'], control['solution_module'], control['theorem_names']),
                                 ('VerifierChallenge', 'OAI.Combinatorics.ProgressionColoring.Main', [TARGET]))


if __name__ == '__main__':
    unittest.main()
