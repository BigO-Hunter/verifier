"""Zeta zeros on the critical line: the upstream rerun profile (Lead, 2026-11-05, task 5caf7b44). Anthropic's
zeta23/Challenge.lean, byte for byte, with one target, montgomery_taylor_simple_on_critical_line_mult_cumulative
(kappa* >= 2 - 1/cMT = 3/2 - cot(1/sqrt 2)/sqrt 2), on their pins Lean v4.33.0-rc2 and Mathlib 51e6992e. Closed: only a
maintainer dispatch of verify.yml runs it; the issue and PR routes do not list the problem."""
from decimal import Decimal, getcontext
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

PROFILE = json.loads((v.ROOT / 'profiles/critical-line-zeros.json').read_text())
PROVENANCE = json.loads((v.ROOT / 'challenges/critical-line-zeros/provenance.json').read_text())
FOLDER = v.ROOT / 'challenges/critical-line-zeros'
MATHLIB = '51e6992efd06126df61a496bebf8f49482a4e129'
TARGET = 'montgomery_taylor_simple_on_critical_line_mult_cumulative'
REQUEST = {'repo_url': 'https://github.com/anthropics/formal-math',
           'commit': '16a5ce41304fcdaea4e0be7c132e1c361dc26da5',
           'challenge_file': 'challenges/critical-line-zeros/Challenge.lean',
           'theorem_names': TARGET,
           'lean_toolchain': 'leanprover/lean4:v4.33.0-rc2'}


def git_blob(path):
    data = path.read_bytes()
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


class FrozenFilesTests(unittest.TestCase):
    def test_challenge_license_notice_and_manifest_are_the_upstream_bytes(self):
        challenge = v.ROOT / PROFILE['challenge_file']
        self.assertEqual(v.digest(challenge), PROFILE['challenge_sha256'])
        self.assertEqual(v.digest(challenge), PROVENANCE['sha256'])
        self.assertEqual(git_blob(challenge), PROVENANCE['git_blob'])
        self.assertEqual(git_blob(FOLDER / 'LICENSE'), PROVENANCE['license_git_blob'])
        self.assertEqual(git_blob(FOLDER / 'NOTICE'), PROVENANCE['notice_git_blob'])
        self.assertEqual(git_blob(v.ROOT / PROFILE['manifest_file']), PROVENANCE['manifest_git_blob'])
        self.assertEqual(PROVENANCE['source_commit'], PROFILE['upstream_commit'])
        self.assertEqual(PROVENANCE['source_commit'], REQUEST['commit'])

    def test_the_target_is_the_cumulative_simple_theorem_with_the_constant_cMT(self):
        text = (v.ROOT / PROFILE['challenge_file']).read_text()
        self.assertIn(f'theorem {TARGET} :\n    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount 0 T : ℝ) '
                      '≤ N0simple 0 T := by\n  sorry', text)
        self.assertIn('def cMT : ℝ :=\n  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) / '
                      '(1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))', text)
        self.assertIn('def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ', text)
        self.assertIn('def N0simple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard',
                      text)
        # The trusted file imports Mathlib only.
        self.assertEqual([line for line in text.splitlines() if line.startswith('import')], ['import Mathlib'])
        self.assertEqual(PROFILE['theorem_names'], [TARGET])
        self.assertEqual(set(PROFILE['permitted_axioms']), set(v.AXIOMS))

    def test_two_minus_one_over_cMT_is_the_board_constant_H(self):
        # 1/cMT = (1 + t tan t)/(sqrt2 tan t) = cot(t)/sqrt2 + 1/2 at t = 1/sqrt2, so 2 - 1/cMT = 3/2 - cot(t)/sqrt2.
        getcontext().prec = 60
        t = 1 / Decimal(2).sqrt()
        def series(x, n, term):
            total = Decimal(0)
            while abs(term) > Decimal(10) ** -58:
                total += term; term *= -x * x / ((n + 1) * (n + 2)); n += 2
            return total
        sin, cos = series(t, 1, t), series(t, 0, Decimal(1))
        tan = sin / cos
        c_mt = Decimal(2).sqrt() * tan / (1 + t * tan)
        h = Decimal(3) / 2 - t * cos / sin
        self.assertLess(abs((2 - 1 / c_mt) - h), Decimal(10) ** -50)
        self.assertEqual(str(h)[:16], '0.67250070367941')

    def test_manifest_pins_their_mathlib_and_full_revisions(self):
        manifest = json.loads((v.ROOT / PROFILE['manifest_file']).read_text())
        revs = {p['name']: p['rev'] for p in manifest['packages']}
        self.assertEqual(revs['mathlib'], MATHLIB)
        self.assertTrue(all(v.SHA.fullmatch(r) for r in revs.values()))
        self.assertIn(f'rev = "{MATHLIB}"', v.lakefile(PROFILE['source_roots'], PROFILE['manifest_file']))

    def test_rc2_tools_change_only_comparator_and_lean4export(self):
        new = json.loads((v.ROOT / PROFILE['tools_file']).read_text())
        old = json.loads((v.ROOT / 'profiles/anthropic-tools.json').read_text())
        self.assertEqual({k for k in new if new[k] != old[k]}, {'comparator', 'lean4export'})
        # Comparator 7892797 (the merge of #65, fix #64) is the last comparator commit on Lean v4.33.0-rc2, and its
        # manifest pins lean4export 9fb131bb (tag v4.33.0-rc2). Their CI pin 57567492 is on v4.34.0-rc1 and does not
        # build with rc2 (run 41964266185, 2026-11-05: no Lean.Kernel.Environment.replay).
        self.assertEqual(new['comparator'], '789279735fe44c1c05dc54bb9f46ba4d9b8c7611')
        self.assertEqual(new['lean4export'], '9fb131bb100eb32ccf6836f14e4f8328d13b6792')


class RequestTests(unittest.TestCase):
    def test_the_maintainer_request_selects_this_profile(self):
        profile, names = v.validate_request(dict(REQUEST))
        self.assertEqual(profile, PROFILE)
        self.assertEqual(names, [TARGET])

    def test_other_toolchains_and_names_are_refused(self):
        for toolchain in ['leanprover/lean4:v4.33.1', 'leanprover/lean4:v4.34.1']:
            with self.assertRaisesRegex(ValueError, 'toolchain'):
                v.validate_request(dict(REQUEST, lean_toolchain=toolchain))
        # The other 16 theorems of the file are not targets: the dyadic form, 2/3, Dirichlet, and Race.bound.
        for name in ['montgomery_taylor_simple_on_critical_line_mult', 'two_thirds_simple_on_critical_line_cumulative',
                     'dirichlet_montgomery_taylor_simple_on_critical_line_mult', 'Race.bound']:
            with self.assertRaisesRegex(ValueError, 'theorem_names'):
                v.validate_request(dict(REQUEST, theorem_names=name))

    def test_closed_to_issues_and_prs(self):
        self.assertNotIn('critical-line-zeros', json.loads((v.ROOT / 'profiles/direct.json').read_text()))

    def test_their_lean_default_auto_implicit(self):
        # Their lakefile leaves autoImplicit at Lean's default (true).
        self.assertIs(PROFILE['auto_implicit'], True)
        self.assertIn('autoImplicit = true', v.lakefile(PROFILE['source_roots'], PROFILE['manifest_file'], True))


class PrepareTests(unittest.TestCase):
    def test_their_folder_stages_without_their_challenge_or_build_files(self):
        files = {'README.md': 'outside the folder',
                 'eth/Other.lean': 'theorem untrusted : False := sorry\n',
                 'zeta23/Challenge.lean': 'theorem untrusted : False := sorry\n',
                 'zeta23/Solution.lean': 'import ChallengeDeps\nimport Zeta23.ThmD.Mult\n',
                 'zeta23/Solution/XiPrime.lean': 'import Mathlib\n',
                 'zeta23/ChallengeDeps.lean': 'import Mathlib\n',
                 'zeta23/Zeta23/ThmD/Mult.lean': 'import Zeta23.ThmD.Functional\n',
                 'zeta23/Zeta23/ThmD/Functional.lean': 'import Mathlib\n',
                 'zeta23/scripts/PrintAxioms.lean': 'theorem untrusted : False := sorry\n',
                 'zeta23/lakefile.toml': 'untrusted build file', 'zeta23/lake-manifest.json': '{}',
                 'zeta23/comparator.json': '{}',
                 # A submission-side copy of the statement never becomes the target.
                 'zeta23/VerifierChallenge.lean': f'theorem {TARGET} : True := trivial\n'}
        def clone(url, sha, dest, label, **kwargs):
            self.assertEqual((url, sha, label), (REQUEST['repo_url'], REQUEST['commit'], 'submission'))
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
                self.assertEqual(set(hashes), {'Solution.lean', 'Solution/XiPrime.lean', 'ChallengeDeps.lean',
                                               'Zeta23/ThmD/Mult.lean', 'Zeta23/ThmD/Functional.lean'})
                stage = root / 'work/stage'
                self.assertEqual((stage / 'VerifierChallenge.lean').read_bytes(), (v.ROOT / PROFILE['challenge_file']).read_bytes())
                self.assertEqual((stage / 'lean-toolchain').read_text(), 'leanprover/lean4:v4.33.0-rc2\n')
                self.assertEqual((stage / 'lake-manifest.json').read_bytes(), (v.ROOT / PROFILE['manifest_file']).read_bytes())
                self.assertIn(f'rev = "{MATHLIB}"', (stage / 'lakefile.toml').read_text())
                chains = json.loads((root / 'work/control/chains.json').read_text())
                self.assertEqual(sorted(m for chain in chains for m in chain),
                                 ['ChallengeDeps', 'Solution', 'Zeta23.ThmD.Functional', 'Zeta23.ThmD.Mult'])
                control = json.loads((root / 'work/control/lean.json').read_text())
                self.assertEqual((control['challenge_module'], control['solution_module'], control['theorem_names']),
                                 ('VerifierChallenge', 'Solution', [TARGET]))


if __name__ == '__main__':
    unittest.main()
