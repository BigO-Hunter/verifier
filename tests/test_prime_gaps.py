import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
CHALLENGE = ROOT / 'challenges/prime-gaps'


class PrimeGapsStatementTests(unittest.TestCase):
    def test_the_statement_imports_only_mathlib_and_has_no_proof(self):
        text = (CHALLENGE / 'Statement.lean').read_text()
        imports = [line for line in text.splitlines() if line.startswith('import')]
        self.assertEqual(imports, ['import Mathlib.Data.Nat.Nth', 'import Mathlib.Data.Nat.Prime.Defs',
                                   'import Mathlib.Order.Filter.AtTopBot.Basic'])
        self.assertNotIn('sorry', text)
        self.assertNotIn('axiom', text.replace('Axiom Math', ''))

    def test_the_target_is_axiom_math_conclusion_with_b(self):
        # AxiomMath/PrimeGapsLib@1faa7b1 PrimeGaps/Bounded246.lean, with 246 replaced by B.
        provenance = json.loads((CHALLENGE / 'provenance.json').read_text())
        self.assertEqual(provenance['source_commit'], '1faa7b14e82ddebc2772dfb9153922f01b106477')
        original = provenance['original_statement']
        self.assertTrue(original.endswith('≤ 246'))
        text = (CHALLENGE / 'Statement.lean').read_text()
        self.assertIn('def Bound (B : ℕ) : Prop :=\n  ' + original.removesuffix('246') + 'B\n', text)
        self.assertIn('namespace BigOSpeedrun.PrimeGaps', text)

    def test_the_reviewed_statement_bytes(self):
        digest = hashlib.sha256((CHALLENGE / 'Statement.lean').read_bytes()).hexdigest()
        self.assertEqual(digest, 'c6b81e94927315c805bd34a30796d8d757156790dff243287811f3c53494f969')


if __name__ == '__main__':
    unittest.main()
