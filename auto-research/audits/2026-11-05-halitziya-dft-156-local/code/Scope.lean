/-
Audit scope probe for the DFT submission saving pi/1000 (bigospeedrun/verifier
PR #156, HalitZiyaKARTAL/bigO-dft-verifier @
da94a2a6f593caa1f534f1ab1c84b88ff5d74906).

Compiled with `lake env lean` against the staged audit build of the submission
(Lean 4.34.1, mathlib d13f23b). It checks, inside Lean's kernel:

1. `Race.bound` in `Submission.lean` discharges, verbatim and up to defeq, the
   exact target the verifier generates for this bound
   (scripts/submissions.py `challenge_source`, problem dft, bound
   31415926535897932384626433/10000000000000000000000000000).
2. The `DFTProgram` predicate inside that statement expands by `rfl` to the
   full all-lengths exact scalar/index RAM specification.
3. The stated saving constant is exactly `Real.pi / 1000`, the board's reduced
   fraction is at most `pi/1000` (the submission's own `PiCut.cut_le_pi_div`),
   and `pi/1000` is strictly below the certified rate point `67/21280`
   (via the submission's `SeamTB19.pi_lt_TB19`, `pi < 3927/1250 = 3.1416`),
   so the stated exponent has honest margin below the machinery's certificate.
-/

import Submission

open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty Filter Asymptotics

namespace AuditScope

/-- 1. The verifier's generated target at this bound, restated verbatim and
discharged by the submission's own theorem. A mismatch of any named constant
(`DFTProgram`, `=O`, `atTop`, the rational literal) fails to elaborate. -/
theorem verifier_target : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (31415926535897932384626433 : ℝ) / 10000000000000000000000000000)) :=
  Race.bound

/-- 2. The statement's program predicate expands, by `rfl`, to the full
specification with every quantifier and clause visible: work cap on W itself,
peak/value bounds on the supplied root, validity, and exact DFT output for all
inputs at all positive lengths. -/
example
    (order : RAM.Prog false RAM.Ty.w RAM.Ty.w)
    (solve : RAM.Prog false dftInKind dftOutKind) (W : ℕ → ℕ) :
    DFTProgram order solve W =
      (∃ cBound : ℕ, ∀ n : ℕ, 0 < n →
        let cap := (n + 2) ^ cBound
        let d := run order n
        W n + 10 * (n + 2) ≤ cap ∧ d.peak ≤ cap ∧ d.valid ∧
          0 < d.val ∧ d.val < 1024 * n ^ 3 ∧ d.val ≤ cap ∧
          ∀ x : Vec n,
            let result := run solve (n, root d.val, (⟨n, x⟩ : Tape ℂ))
            result.valid ∧ result.peak ≤ cap ∧ d.work + 1 + result.work ≤ W n ∧
              result.val = (⟨n, dft n x⟩ : Tape ℂ)) := rfl

/-- 3. The stated saving is the literal `Real.pi / 1000`; the board's reduced
fraction is at most it; and the saving is strictly below the certified rate
point `67/21280 = 0.0031484962…` (seam `3148496240/10^12`), so the stated
exponent leaves honest margin rather than rounding past the certificate. -/
example : statedSavingTB19 = (Real.pi : ℝ) / 1000 ∧
    (31415926535897932384626433 : ℝ) / 10000000000000000000000000000 ≤ Real.pi / 1000 ∧
    Real.pi / 1000 < 67 / 21280 := by
  refine ⟨rfl, PiCut.cut_le_pi_div, ?_⟩
  have hpi : (Real.pi : ℝ) < 3927 / 1250 := SeamTB19.pi_lt_TB19
  have hbridge : (3927 / 1250 : ℝ) / 1000 < 67 / 21280 := by norm_num
  linarith

end AuditScope

#print axioms AuditScope.verifier_target
