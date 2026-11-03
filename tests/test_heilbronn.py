import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
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


if __name__ == '__main__':
    unittest.main()
