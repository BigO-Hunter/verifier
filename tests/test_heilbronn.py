import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s

CHALLENGE = ROOT / 'challenges/heilbronn-triangle'
FROZEN = CHALLENGE / 'OAI/Geometry/HeilbronnTriangle/Definitions.lean'


class HeilbronnStatementTests(unittest.TestCase):
    def test_the_verifier_statement_is_the_reviewed_files_joined(self):
        # One self-contained challenge (Lead, 2026-11-03, verifier #105): the verifier stages no OAI module path.
        first, rest = (CHALLENGE / 'Statement.lean').read_text().split('\n', 1)
        self.assertEqual(first, 'import OAI.Geometry.HeilbronnTriangle.Definitions')
        joined = (CHALLENGE / 'VerifierStatement.lean').read_text()
        self.assertEqual(joined, FROZEN.read_text() + rest)
        self.assertEqual([line for line in joined.splitlines() if line.startswith('import')], ['import Mathlib'])
        self.assertNotIn('sorry', joined)
        self.assertEqual(hashlib.sha256(joined.encode()).hexdigest(),
                         'efc9772011b2104ba2cb51bd672e1bb974ab1a29f2384922e1c62f54307e32cb')

    def test_the_openai_definitions_are_unchanged(self):
        # openai/math@1581d4c lean/OAI/Geometry/HeilbronnTriangle/Definitions.lean, frozen byte for byte (PR #20).
        entry = json.loads((CHALLENGE / 'provenance.json').read_text())['files'][0]
        self.assertEqual(entry['original_path'], 'lean/OAI/Geometry/HeilbronnTriangle/Definitions.lean')
        raw = FROZEN.read_bytes()
        self.assertEqual((hashlib.sha256(raw).hexdigest(), len(raw)), (entry['sha256'], entry['bytes']))
        self.assertEqual(entry['sha256'], 'e0d75ecc36327321392b4d3c8f08cc7ecfcf678cdc47ccfde314fb8dd9c9196d')
        self.assertTrue((CHALLENGE / 'VerifierStatement.lean').read_bytes().startswith(raw))

    def test_the_target_is_the_reviewed_parameterization(self):
        statement = (CHALLENGE / 'Statement.lean').read_text()
        self.assertIn('def Bound (η : ℚ) : Prop :=', statement)
        for part in ['∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →', 'P.card = n ∧ pointsInUnitSquare P ∧',
                     'triangleAreasAtLeast P (c * Real.rpow (n : ℝ) (-2 + (η : ℝ)))']:
            self.assertIn(part, statement)

    def test_validation_imports_the_verifier_statement(self):
        validation = (CHALLENGE / 'Validation.lean').read_text()
        self.assertTrue(validation.startswith('import VerifierStatement\n'))
        self.assertNotIn('sorry', validation)
        for name in ['bound_mono', 'bound_zero', 'not_bound_of_two_lt', 'nonvacuous']:
            self.assertIn(f'#print axioms BigOSpeedrun.HeilbronnTriangle.{name}', validation)


def body(bound='1/50893237'):
    return ('### Problem\n\nheilbronn-triangle\n\n### Repository URL\n\nhttps://github.com/someone/heilbronn-lean\n\n'
            f'### Commit SHA\n\n{"a" * 40}\n\n### Bound\n\n{bound}\n')


class ProfileTests(unittest.TestCase):
    def test_the_profile_pins_the_reviewed_statement(self):
        # Lead, 2026-11-03 (verifier #105): Lean v4.34.1 + Mathlib d13f23b, one job, a saving 0 < eta <= 5/6.
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['heilbronn-triangle']
        self.assertEqual(profile['challenge_file'], 'challenges/heilbronn-triangle/VerifierStatement.lean')
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256((ROOT / profile['challenge_file']).read_bytes()).hexdigest())
        self.assertEqual(profile['challenge_sha256'], 'efc9772011b2104ba2cb51bd672e1bb974ab1a29f2384922e1c62f54307e32cb')
        self.assertEqual((profile['lean_toolchain'], profile['manifest_file'], profile['tools_file']),
                         ('leanprover/lean4:v4.34.1', 'profiles/lake-manifest.json', 'profiles/tools.json'))
        self.assertEqual((profile['theorem_names'], profile['source_roots'], profile['maximum'], profile['bound_kind'], profile['upstream_commit']),
                         (['Race.bound'], ['Submission'], '5/6', 'saving', '1581d4cbdd69a0faf34b2089614fe2a814316a6a'))
        self.assertNotIn('runner', profile)
        self.assertEqual(s.matrix_entry(5, 'x', 'issue', s.parse_body(body())), {'issue_number': 5, 'login': 'x', 'route': 'issue'})
        self.assertEqual((s.MODEL_IDS['heilbronn-triangle'], s.board_line('heilbronn-triangle')),
                         ('other/heilbronn-triangle', 'Heilbronn triangle board: https://bigospeedrun.com/other/heilbronn-triangle'))

    def test_target_and_positive_bounds(self):
        sub = s.parse_body(body())
        source = s.challenge_source(sub)
        self.assertTrue(source.startswith((CHALLENGE / 'VerifierStatement.lean').read_text()))
        self.assertTrue(source.endswith('theorem Race.bound : BigOSpeedrun.HeilbronnTriangle.Bound ((1 : ℚ) / 50893237) := by\n  sorry\n'))
        self.assertTrue(s.challenge_source(dict(sub, bound='2/100866719')).endswith('Bound ((2 : ℚ) / 100866719) := by\n  sorry\n'))
        for good in ['1/50893237', '5/6', '1/' + '9' * 40, '1/2']:
            self.assertEqual(s.validate_submission(dict(sub, bound=good))['bound'], good)
        # eta = 0 is refused (Lead, 2026-11-03): the vacuous classical bound. Above 5/6 is false (out of range).
        with self.assertRaisesRegex(ValueError, 'must be positive for heilbronn-triangle'):
            s.validate_submission(dict(sub, bound='0'))
        for bad in ['6/7', '1', '1/' + '1' + '0' * 40, '0.5', '-1/2']:
            with self.subTest(bound=bad), self.assertRaises(ValueError):
                s.validate_submission(dict(sub, bound=bad))


class GateTests(unittest.TestCase):
    def gate(self, claims=(), direct=None, direction='higher'):
        rows = {'families': [{'slug': 'heilbronn-triangle', 'direction': direction, 'claims': list(claims)}]}
        files = {'src/lib/other-bounds.json': json.dumps(rows).encode(),
                 'data/direct-other.json': None if direct is None else json.dumps({'boards': {'other-heilbronn-triangle': {'claims': direct}}}).encode(),
                 'data/prove2me.json': None}
        with patch.object(s, 'site_files', return_value=('c' * 40, files)):
            return s.current_record('heilbronn-triangle', 'https://github.com/bigospeedrun/verifier/issues/120')

    def run_for(self, bound, record):
        return s.qualifies_for_run({'problem': 'heilbronn-triangle', 'bound': bound}, record)

    def test_a_higher_saving_is_better_and_claimed_rows_never_gate(self):
        # The first Other bounds row where a higher bound is better. The Claimed rows (canghaimeng 2/100866719, and
        # littleBro's rows, whose values are not exact rationals) never gate.
        claimed = [{'handle': 'canghaimeng', 'value': '2/100866719', 'evidence': 'claimed', 'url': 'x'},
                   {'handle': 'littleBro', 'value': '1/(498\\cdot379^{17}+7)', 'evidence': 'claimed', 'url': 'y'}]
        record = self.gate(claimed)
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound'], record['problem_id']),
                         ('0', ['profile-range'], False, 'other/heilbronn-triangle'))
        self.assertTrue(self.run_for('1/' + '9' * 40, record))
        self.assertTrue(self.run_for('5/6', record))
        # The largest Lean Verified saving gates: it again does not run, a larger one does, a smaller one does not.
        record = self.gate(claimed, direct=[{'handle': 'direct-issue-121', 'value': '1/1000', 'evidence': 'lean-verified', 'url': 'z'},
                                            {'handle': 'direct-issue-122', 'value': '1/2000', 'evidence': 'lean-verified', 'url': 'w'}])
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('1/1000', ['direct-issue-121'], True))
        self.assertFalse(self.run_for('1/1000', record))
        self.assertTrue(self.run_for('1/999', record))
        self.assertFalse(self.run_for('1/1001', record))
        # The site row must say that a higher saving is better.
        with self.assertRaisesRegex(ValueError, 'direction mismatch'):
            self.gate(claimed, direction='lower')

    def test_the_lower_is_better_rows_are_unchanged(self):
        self.assertEqual(s.HIGHER, {'dft', 'heilbronn-triangle'})
        for problem in ['3sum', 'apsp', 'subset-sum', 'average-sensitivity', 'catalan', 'snaky']:
            self.assertEqual(s.open_rank(problem), 1)
            self.assertTrue(s.qualifies_for_run({'problem': problem, 'bound': '1/3'}, {'score': '1/2', 'score_relation': 'attained'}))
        self.assertEqual((s.open_rank('dft'), s.range_end('dft')), (-1, 0))
        self.assertEqual(s.range_end('heilbronn-triangle'), 0)


class ClosedTests(unittest.TestCase):
    def test_heilbronn_is_closed_until_its_smoke(self):
        self.assertIn('heilbronn-triangle', s.CLOSED)


if __name__ == '__main__':
    unittest.main()
