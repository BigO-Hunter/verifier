import Submission

/-! Independent scope probe for the 3SUM submission at 384055881637/200000000000.

`Submission/EndStatement.lean` is copied byte for byte from the verifier's
`challenges/3sum-apsp/EndStatement.lean` (sha256 4291e3f0…), so the trusted
definitions are the ones elaborated here. This file restates the verifier's
generated target verbatim, closes it with the submission's own public theorem,
and unfolds the definitions below it so that any substitution or weakening
would fail to elaborate. -/

-- 1. The verifier's generated `Race.bound` target, at the submitted bound,
--    discharged by the submission's own theorem.
example : EndStatement.ThreeSum.SolvedInTime ((384055881637 : Rat) / 200000000000) :=
  Race.bound

-- 2. The bound is the claimed rational, in lowest terms, strictly under the
--    profile maximum 2, the paper's own Theorem 22 exponent 1.9992, the
--    previously verified 96013971/50000000 (issue #92), and the prior 3SUM
--    record the development's own certificate says it beats.
example : Nat.gcd 384055881637 200000000000 = 1 := by decide
example : ((384055881637 : Rat) / 200000000000 : Rat) < 2 := by norm_num
example : ((384055881637 : Rat) / 200000000000 : Rat) < (9996 : Rat) / 5000 := by norm_num
example : ((384055881637 : Rat) / 200000000000 : Rat) < (96013971 : Rat) / 50000000 := by norm_num
example : ((384055881637 : Rat) / 200000000000 : Rat)
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
example : EndStatement.ThreeSum.SolvedInTime ((384055881637 : Rat) / 200000000000) =
    (∀ κ : Nat, ∃ (P : List EndStatement.Instr) (b : Nat) (T : Nat → Nat),
      EndStatement.BigO T ((384055881637 : Rat) / 200000000000) ∧
        ∀ (n : Nat) (x : EndStatement.ThreeSum.Instance n),
          (∀ a ∈ EndStatement.ThreeSum.input x, a.natAbs ≤ n ^ κ) →
          ∀ W ≥ b * (Nat.log2 n + 1),
            EndStatement.ThreeSum.SolvedBy x P W (T n)) := rfl

-- 6. Bound vs the development's own cost-ledger certificate: the six-term
--    ledger is proven below the certificate exponent 2400349260231/1250000000000,
--    which the development itself places strictly below the submitted bound.
example : ThreeSum.WeightedGlobalParameters.targetExponent
    = (384055881637 : ℝ) / 200000000000 := rfl
example : ∀ t ∈ ThreeSum.WeightedGlobalParameters.costLedger,
    t < (384055881637 : ℝ) / 200000000000 :=
  ThreeSum.WeightedGlobalParameters.all_costs_lt_target
example : ThreeSum.WeightedGlobalParameters.certificateExponent
    < (384055881637 : ℝ) / 200000000000 :=
  ThreeSum.WeightedGlobalParameters.certificate_lt_target

-- 7. Axiom controllers. The third reads an `opaque` package, to show the
--    reported closure is not blind to bodies hidden behind `opaque`.
#print axioms Race.bound
#print axioms ThreeSum.optimized_solvedInTime_384055881637_200000000000
#print axioms ThreeSum.WeightedGlobalOversizePrime.nativePrime_eq_selected
