import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
CHALLENGE = ROOT / 'challenges/other-snaky'


class SnakyStatementTests(unittest.TestCase):
    def test_the_verifier_statement_is_the_reviewed_files_joined(self):
        # One self-contained challenge: staging Statement.lean's import would take Model.lean from the submitter.
        model = (CHALLENGE / 'Model.lean').read_text()
        first, rest = (CHALLENGE / 'Statement.lean').read_text().split('\n', 1)
        self.assertEqual(first, 'import challenges.«other-snaky».Model')
        joined = (CHALLENGE / 'VerifierStatement.lean').read_text()
        self.assertEqual(joined, model + rest)
        imports = [line for line in joined.splitlines() if line.startswith('import')]
        self.assertEqual(imports, ['import Mathlib.Data.Finset.Card', 'import Mathlib.Data.Int.Basic',
                                   'import Mathlib.Data.Fintype.Prod', 'import Mathlib.Algebra.Group.Prod'])
        self.assertNotIn('sorry', joined)

    def test_the_openai_block_is_unchanged(self):
        # openai/math@1581d4c lean/ComparatorChallenges/SnakyTwentyOne.lean, lines 3-40 (the definitions).
        provenance = json.loads((CHALLENGE / 'provenance.json').read_text())
        self.assertEqual(provenance['source_commit'], '1581d4cbdd69a0faf34b2089614fe2a814316a6a')
        self.assertEqual(provenance['extracted_lines'], '3-40')
        lines = (CHALLENGE / 'Model.lean').read_text().splitlines(keepends=True)
        start, end = map(int, provenance['local_lines'].split('-'))
        block = ''.join(lines[start - 1:end])
        self.assertEqual(hashlib.sha256(block.encode()).hexdigest(), provenance['extracted_sha256'])
        self.assertEqual(provenance['extracted_sha256'], '0d999f2d9ea7a88ee3a28067de5ac85566e4541c0763b006b30c4b6a30abf638')
        self.assertTrue(block.startswith('namespace OAI\n') and block.endswith('end SnakyPrototype.OrdinaryStrategy\n'))
        self.assertEqual(''.join(lines[end:]), '\nend OAI\n')

    def test_the_target_keeps_openai_conclusion_with_n(self):
        statement = (CHALLENGE / 'Statement.lean').read_text()
        for part in ['∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B', 'LegalRepliesBeforeFinal σ n β ∅ ∅',
                     'HasSnaky (playState σ n β ∅ ∅ n).1', '(playState σ n β ∅ ∅ n).1.card = n',
                     'Disjoint (playState σ n β ∅ ∅ n).1 (playState σ n β ∅ ∅ (n - 1)).2',
                     '(playState σ n β ∅ ∅ k).2.card = k']:
            self.assertIn(part, statement)
        self.assertIn('def Bound (n : ℕ) : Prop :=', statement)


if __name__ == '__main__':
    unittest.main()
