import Submission

/-! Independent scope probe for the 3SUM submission at 96013971/50000000.

`Submission/EndStatement.lean` is copied byte for byte from the verifier's
`challenges/3sum-apsp/EndStatement.lean` (sha256 4291e3f0…), so the trusted
definitions are the ones elaborated here. This file restates the verifier's
generated target verbatim, closes it with the submission's own public theorem,
and unfolds the definitions below it so that any substitution or weakening
would fail to elaborate. -/

-- 1. The verifier's generated `Race.bound` target, at the submitted bound,
--    discharged by the submission's own theorem.
example : EndStatement.ThreeSum.SolvedInTime ((96013971 : Rat) / 50000000) :=
  Race.bound

-- 2. The bound is the claimed rational, in lowest terms, strictly under both
--    the profile maximum 2 and the paper's own Theorem 22 exponent 1.9992.
example : Nat.gcd 96013971 50000000 = 1 := by decide
example : ((96013971 : Rat) / 50000000 : Rat) < 2 := by norm_num
example : ((96013971 : Rat) / 50000000 : Rat) < (9996 : Rat) / 5000 := by norm_num
-- the prior 3SUM record the submission's own certificate says it beats
example : ((96013971 : Rat) / 50000000 : Rat)
    < (4800698571997281331 : Rat) / 2500000000000000000 := by norm_num

-- 3. `ThreeSum` is the trusted problem: three distinct positions summing to 0.
example : ∀ {n : Nat} (x : EndStatement.ThreeSum.Instance n),
    (EndStatement.ThreeSum.yes x ↔
      ∃ i j k : Fin n, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i + x j + x k = 0) := by
  intro n x
  exact Iff.rfl

-- 4. `ThreeSum` imposes no output condition (the trusted default `True`).
example : ∀ {n : Nat} (x : EndStatement.ThreeSum.Instance n) (out : Nat → Int),
    (EndStatement.ThreeSum.output x out ↔ True) := by
  intro n x out
  exact Iff.rfl

-- 5. `SolvedInTime` unfolds to the trusted for-every-κ word-RAM form, with
--    the `n^κ` magnitude hypothesis and the `b·(⌊log₂n⌋+1)` word-size floor.
example : EndStatement.ThreeSum.SolvedInTime ((96013971 : Rat) / 50000000) =
    (∀ κ : Nat, ∃ (P : List EndStatement.Instr) (b : Nat) (T : Nat → Nat),
      EndStatement.BigO T ((96013971 : Rat) / 50000000) ∧
        ∀ (n : Nat) (x : EndStatement.ThreeSum.Instance n),
          (∀ a ∈ EndStatement.ThreeSum.input x, a.natAbs ≤ n ^ κ) →
          ∀ W ≥ b * (Nat.log2 n + 1),
            EndStatement.ThreeSum.SolvedBy x P W (T n)) := rfl

-- 6. Axiom controllers. The third reads an `opaque` package, to show the
--    reported closure is not blind to bodies hidden behind `opaque`.
#print axioms Race.bound
#print axioms ThreeSum.weighted_solvedInTime_96013971_50000000
#print axioms ThreeSum.WeightedGlobalOversizePrime.nativePrime_eq_selected
