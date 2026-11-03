import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s

CHALLENGE = ROOT / 'challenges/directed-sssp'
FORK = 'https://github.com/bigospeedrun/c-hd-proof'
PIN = '98c53accb47a505482a1781597ae14bf67e81cec'


def body(bound='n log^3/4 ; n log^11/12'):
    return ('### Problem\n\ndirected-sssp\n\n### Repository URL\n\nhttps://github.com/someone/sssp-lean\n\n'
            f'### Commit SHA\n\n{"a" * 40}\n\n### Bound\n\n{bound}\n')


class StatementTests(unittest.TestCase):
    def test_the_statement_imports_the_model_and_no_proof(self):
        # Nil's GO, 2026-11-03: the model comes from our fork at a pinned commit; this file has the race statement only.
        statement = (CHALLENGE / 'VerifierStatement.lean').read_text()
        self.assertEqual([line for line in statement.splitlines() if line.startswith('import')],
                         ['import Frontier.CostModel', 'import Mathlib.Analysis.SpecialFunctions.Pow.Real'])
        for word in ['sorry', 'axiom', 'admit', 'theorem', 'lemma']:
            self.assertNotIn(word, statement)
        for part in ['(n : ℝ) ^ (a : ℝ) * (⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b : ℝ)⌋₊ : ℝ)',
                     '(n : ℝ) ^ (a : ℝ) * Real.log n ^ (b : ℝ) * Real.log (Real.log n) ^ (c : ℝ)',
                     '∃ fuel r, P.run fuel G s = some r ∧ r.Solves G s ∧ (r.cost : ℝ) ≤ budget',
                     '∃ P : Program, P.Exact ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 16 ≤ N ∧',
                     '(∀ (G : Graph) (s : Fin G.n), N ≤ G.n → Sparse a b G.n G.m →\n      CorrectWithin P G s (C * Time a\' b\' c\' G.n)) ∧',
                     '(∀ (G : Graph) (s : Fin G.n),\n      CorrectWithin P G s (C * ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)))']:
            self.assertIn(part, statement)

    def test_validation_imports_the_verifier_statement(self):
        validation = (CHALLENGE / 'Validation.lean').read_text()
        self.assertTrue(validation.startswith('import VerifierStatement\n'))
        self.assertNotIn('sorry', validation)
        for name in ['weaker_time', 'cover_sparser', 'cap_ge_self', 'time_pos']:
            self.assertIn(f'theorem {name}' if name != 'time_pos' else f'lemma {name}', validation)

    def test_the_profile_pins_the_statement_and_the_fork(self):
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['directed-sssp']
        self.assertEqual(profile['challenge_file'], 'challenges/directed-sssp/VerifierStatement.lean')
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256((ROOT / profile['challenge_file']).read_bytes()).hexdigest())
        self.assertEqual((profile['lean_toolchain'], profile['manifest_file'], profile['tools_file']),
                         ('leanprover/lean4:v4.34.1', 'profiles/lake-manifest.json', 'profiles/tools.json'))
        self.assertEqual((profile['theorem_names'], profile['source_roots'], profile['upstream_commit']),
                         (['Race.bound'], ['Submission'], PIN))
        # The fork is cloned at its pin and staged as the Frontier root; no file of it is in this repository, and no
        # patch changes it (Lead, 2026-11-03). Its own build keeps Lean's default autoImplicit = true (formal/lean has
        # no leanOptions), and Frontier/CHD/MergeSort.lean uses an auto-bound name (smoke run 41631927522 failed with
        # autoImplicit = false), so only the Frontier root gets that option; Submission and the challenge keep false.
        self.assertEqual(profile['solution_dependencies'],
                         [{'repo_url': FORK, 'commit': PIN, 'source_subdir': 'formal/lean', 'source_roots': ['Frontier'],
                           'lean_options': {'autoImplicit': True}}])
        sys.path.insert(0, str(ROOT / 'scripts'))
        import verifier
        lake = verifier.lakefile(['Submission', 'Frontier', 'VerifierChallenge', 'VerifierAudit'], root_options=
                                 verifier.dependency_root_options(profile['solution_dependencies'], profile['source_roots']))
        self.assertIn('[leanOptions]\nautoImplicit = false\n', lake)
        self.assertIn('\n[[lean_lib]]\nname = "Frontier"\n[lean_lib.leanOptions]\nautoImplicit = true\n', lake)
        self.assertEqual(lake.count('autoImplicit = true'), 1)
        self.assertFalse((CHALLENGE / 'Frontier').exists())
        self.assertNotIn('runner', profile)

    def test_the_problem_is_closed(self):
        self.assertIn('directed-sssp', s.CLOSED)
        self.assertEqual((s.MODEL_IDS['directed-sssp'], s.board_line('directed-sssp')),
                         ('directed-sssp/comparison-addition-sparse',
                          'Directed shortest paths board: https://bigospeedrun.com/directed-sssp'))


class CHDRowTests(unittest.TestCase):
    """The maintainer profile for the Vals AI row (Lead, 2026-11-03: a maintainer binding, as for matrix-nine-fourths).
    verify.yml checks one fixed target, the C-HD row; the public issue route never reads this profile."""
    def test_the_fixed_target_is_the_generated_c_hd_row(self):
        profile = json.loads((ROOT / 'profiles/sssp-chd.json').read_text())
        direct = json.loads((ROOT / 'profiles/direct.json').read_text())['directed-sssp']
        target = (ROOT / profile['challenge_file']).read_text()
        sub = dict(s.parse_body(body()), bound='n log^3/4 ; n log^11/12')
        self.assertEqual(target, s.challenge_source(sub))
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256(target.encode()).hexdigest())
        self.assertEqual(profile['challenge_sha256'], 'b9569daeed41b0394a8a0ec10bd40fa15d005fef8afb1abfa2f77a52f7d27ab0')
        for key in ['lean_toolchain', 'manifest_file', 'tools_file', 'solution_module', 'theorem_names', 'source_roots',
                    'upstream_commit', 'solution_dependencies']:
            self.assertEqual(profile[key], direct[key], key)
        self.assertEqual((profile['bound'], profile['score_relation'], profile['model']),
                         ('n log^3/4 ; n log^11/12', 'attained', s.MODEL_IDS['directed-sssp']))
        self.assertEqual(set(profile['permitted_axioms']), {'propext', 'Quot.sound', 'Classical.choice'})
        self.assertIn('directed-sssp', s.CLOSED)

    def test_verify_resolves_only_this_profile_for_the_row(self):
        sys.path.insert(0, str(ROOT / 'scripts'))
        import verifier
        request = {'repo_url': 'https://github.com/bigospeedrun/sssp-lean-scratch',
                   'commit': '98919233966fa6196cf67639c1eee2b2496d26b6',
                   'challenge_file': 'challenges/directed-sssp/CHDRow.lean', 'theorem_names': 'Race.bound',
                   'lean_toolchain': 'leanprover/lean4:v4.34.1'}
        profile, names = verifier.validate_request(request)
        self.assertEqual((profile['challenge_file'], names), ('challenges/directed-sssp/CHDRow.lean', ['Race.bound']))
        for field, value in [('theorem_names', 'BigOSpeedrun.DirectedSSSP.Bound'), ('lean_toolchain', 'leanprover/lean4:v4.34.0'),
                             ('challenge_file', 'challenges/directed-sssp/VerifierStatement.lean')]:
            with self.subTest(field=field), self.assertRaises(ValueError):
                verifier.validate_request(dict(request, **{field: value}))


class GrammarTests(unittest.TestCase):
    def test_normal_forms_parse_to_exponent_tuples(self):
        cases = {
            'n log^3/4 ; n log^11/12': (1, F(3, 4), 1, F(11, 12), 0),
            'n ; n log^1/2 loglog^1/2': (1, 0, 1, F(1, 2), F(1, 2)),
            'n ; n log': (1, 0, 1, 1, 0),
            'n^2 ; n^2': (2, 0, 2, 0, 0),
            'n ; n^3': (1, 0, 3, 0, 0),
            'n log^3/4 ; n log^11/12 loglog^-1/3': (1, F(3, 4), 1, F(11, 12), F(-1, 3)),
            'n^3/2 log^2 ; n^3/2 log^2 loglog': (F(3, 2), 2, F(3, 2), 2, 1),
            'n log ; n log^2 loglog^-7': (1, 1, 1, 2, -7),
        }
        for text, tup in cases.items():
            with self.subTest(text=text):
                self.assertEqual(s.parse_sssp(text), tuple(F(x) for x in tup))
                self.assertEqual(s.validate_submission(dict(s.parse_body(body()), bound=text))['bound'], text)

    def test_other_texts_are_refused_with_the_example(self):
        for text in ['n log^3/4; n log^11/12', 'n log^3/4 ;n log^11/12', 'n log^6/8 ; n log', 'n^1 ; n', 'log n ; n',
                     'n log^0 ; n', 'n loglog ; n', 'n ; n log  loglog', ' n ; n', 'n ; n ', 'n ; n ; n', 'n ; n^01',
                     'n ; n^+2', 'n ; n^2.5', 'n ; loglog log n', 'n ; n n', 'n ; n log^1/1', 'n ; n log^-0',
                     'n ; n log^2/-3', 'n^2 ;', '; n', 'n', '', 'n ; n log^' + '1' * 41, 'n ; N', 'n ; n lg',
                     'n ; n\tlog', 'n ; n log^3/4\n']:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'for example "n log\\^3/4 ; n log\\^11/12"'):
                s.parse_sssp(text)

    def test_ranges(self):
        for text in ['n log^-1 ; n', 'n^1/2 ; n', 'n^2 log ; n^3', 'n^3 ; n^3']:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'between n and n\\^2'):
                s.parse_sssp(text)
        for text in ['n log ; n', 'n ; n^4', 'n ; n^3 loglog', 'n log ; n log^-1 loglog^9', 'n^2 ; n^2 loglog^-5',
                     'n ; n loglog^-1']:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'at least the edge bound D and at most n\\^3'):
                s.parse_sssp(text)

    def test_up_to_40_digits_per_integer(self):
        self.assertEqual(s.parse_sssp('n ; n log^1/' + '9' * 40)[3], F(1, int('9' * 40)))
        with self.assertRaises(ValueError):
            s.parse_sssp('n ; n log^1/1' + '0' * 40)

    def test_the_issue_form_value_must_be_the_normal_form(self):
        self.assertEqual(s.parse_body(body())['bound'], 'n log^3/4 ; n log^11/12')
        with self.assertRaisesRegex(ValueError, 'for example'):
            s.parse_body(body('n log^0.75 ; n log^11/12'))

    def test_the_target_has_the_five_exact_rationals(self):
        sub = s.parse_body(body())
        source = s.challenge_source(sub)
        self.assertTrue(source.startswith((CHALLENGE / 'VerifierStatement.lean').read_text()))
        self.assertTrue(source.endswith(
            '\n-- Big O Speedrun exact-bound target; generated from validated integers.\n'
            'theorem Race.bound : BigOSpeedrun.DirectedSSSP.Bound ((1 : ℚ) / 1) ((3 : ℚ) / 4) ((1 : ℚ) / 1) '
            '((11 : ℚ) / 12) ((0 : ℚ) / 1) := by\n  sorry\n'))
        self.assertTrue(s.challenge_source(dict(sub, bound='n log ; n log^2 loglog^-7')).endswith(
            'Bound ((1 : ℚ) / 1) ((1 : ℚ) / 1) ((1 : ℚ) / 1) ((2 : ℚ) / 1) ((-7 : ℚ) / 1) := by\n  sorry\n'))

    def test_other_problems_keep_one_rational(self):
        self.assertEqual(s.parse_body(body('1/2').replace('directed-sssp', 'catalan'))['bound'], '1/2')
        with self.assertRaises(ValueError):
            s.parse_body(body('n ; n').replace('directed-sssp', 'catalan'))


if __name__ == '__main__':
    unittest.main()
