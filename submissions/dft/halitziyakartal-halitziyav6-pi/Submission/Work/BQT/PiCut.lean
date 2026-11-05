import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The board's fraction is below `π/1000`

New file, not a copy.  The board's bound field takes a reduced fraction only, so `Race.bound` (Submission.lean) states
the saving `31415926535897932384626433/10^28`: `π/1000`, cut right after π's first 33 (…26433).  It follows from
`Race.bound_pi`, the same result at exactly `π/1000`, by the two facts of this file:
* `PiCut.pi_gt_cut`: `3.1415926535897932384626433 < π`, by the steps of Mathlib's `pi_lower_bound` tactic
  (Mathlib/Analysis/Real/Pi/Bounds.lean, whose own bounds stop at 20 decimals), with 41 rational upper bounds on
  `sqrtTwoAddSeries 0 k = 2 cos (π / 2 ^ (k + 1))`, from a Python port of the Mathematica script quoted in that file
  (`Iters -> 41, Rounding -> 0.6`), checked here by `norm_num`;
* `PiCut.isBigO_saving_mono`: a bound `O(n (log n)^(1 - s))` gives `O(n (log n)^(1 - t))` for every `t ≤ s`
  (from `n = 3` on, `log n ≥ 1`).
-/

open Filter Asymptotics

namespace PiCut

/-- `3.1415926535897932384626433 < π`: π cut right after its first 33 is below π. -/
theorem pi_gt_cut : (31415926535897932384626433 : ℝ) / 10000000000000000000000000 < Real.pi := by
  -- the steps of Mathlib's `pi_lower_bound` tactic, written out: 41 rational upper bounds r_k on
  -- `sqrtTwoAddSeries 0 k`, each with `√(2 + r_(k-1)) ≤ r_k`, and `r_41 ≤ 2 - (a / 2^42)^2` at the end
  apply Real.pi_lower_bound_start 41
  apply Real.sqrtTwoAddSeries_step_up 102845515571962 72722761475561
  apply Real.sqrtTwoAddSeries_step_up 220839524462593 119517489397296
  apply Real.sqrtTwoAddSeries_step_up 333977635198355 170260321943783
  apply Real.sqrtTwoAddSeries_step_up 563993894502275 283361409890311
  apply Real.sqrtTwoAddSeries_step_up 3854351052858199 1929499693311800
  apply Real.sqrtTwoAddSeries_step_up 5153683422922438 2577618041823743
  apply Real.sqrtTwoAddSeries_step_up 14568367622657983 7284732338276388
  apply Real.sqrtTwoAddSeries_step_up 32190847412238832 16095726703625941
  apply Real.sqrtTwoAddSeries_step_up 32214031985891486 16107091795986909
  apply Real.sqrtTwoAddSeries_step_up 134129324473384802 67064741141599453
  apply Real.sqrtTwoAddSeries_step_up 128683368067629773 64341702959097948
  apply Real.sqrtTwoAddSeries_step_up 192209497783032773 96104755958510627
  apply Real.sqrtTwoAddSeries_step_up 899581351429811114 449790683983664399
  apply Real.sqrtTwoAddSeries_step_up 2449112922249190079 1224556466752525150
  apply Real.sqrtTwoAddSeries_step_up 3463538429697076352 1731769216838294547
  apply Real.sqrtTwoAddSeries_step_up 7310821667456256130 3655410834778120311
  apply Real.sqrtTwoAddSeries_step_up 21541588579718811715 10770794290632865463
  apply Real.sqrtTwoAddSeries_step_up 34940563009447899855 17470281505037588752
  apply Real.sqrtTwoAddSeries_step_up 24538951640346803699 12269475820228469422
  apply Real.sqrtTwoAddSeries_step_up 82895081259059953340 41447540629576482639
  apply Real.sqrtTwoAddSeries_step_up 160085780738076823367 80042890369060864597
  apply Real.sqrtTwoAddSeries_step_up 1617283350522626762728 808641675261370089591
  apply Real.sqrtTwoAddSeries_step_up 714769644123713477804 357384822061863004551
  apply Real.sqrtTwoAddSeries_step_up 997056841275472864957 498528420637738617521
  apply Real.sqrtTwoAddSeries_step_up 6438295627024248871140 3219147813512127962939
  apply Real.sqrtTwoAddSeries_step_up 6534180969378417275549 3267090484689209532750
  apply Real.sqrtTwoAddSeries_step_up 960850236298106631071 480425118149053348437
  apply Real.sqrtTwoAddSeries_step_up 36318541481863258997069 18159270740931629809440
  apply Real.sqrtTwoAddSeries_step_up 17101536755901125736109 8550768377950562904654
  apply Real.sqrtTwoAddSeries_step_up 141996092972603262718041 70998046486301631434993
  apply Real.sqrtTwoAddSeries_step_up 77045811899261597284251 38522905949630798652431
  apply Real.sqrtTwoAddSeries_step_up 83957543799787272587143 41978771899893636296379
  apply Real.sqrtTwoAddSeries_step_up 894869293202078128228916 447434646601039064121939
  apply Real.sqrtTwoAddSeries_step_up 1452891650211527997003341 726445825105763998504707
  apply Real.sqrtTwoAddSeries_step_up 3015354249837987629553425 1507677124918993814778288
  apply Real.sqrtTwoAddSeries_step_up 3234496148667850900633841 1617248074333925450317343
  apply Real.sqrtTwoAddSeries_step_up 11927443786093518824114431 5963721893046759412057605
  apply Real.sqrtTwoAddSeries_step_up 20149571274068126794011851 10074785637034063397006090
  apply Real.sqrtTwoAddSeries_step_up 57080244460278097787292513 28540122230139048893646373
  apply Real.sqrtTwoAddSeries_step_up 85252897305479734034239679 42626448652739867017119883
  apply Real.sqrtTwoAddSeries_step_up 317493548585924526748203145 158746774292962263374101613
  simp [Real.sqrtTwoAddSeries]
  all_goals norm_num1

/-- The fraction of `Race.bound` is at most `π/1000`. -/
theorem cut_le_pi_div :
    (31415926535897932384626433 : ℝ) / 10000000000000000000000000000 ≤ Real.pi / 1000 := by
  have h := pi_gt_cut
  linarith

/-- **Monotonicity in the saving**: a bound `O(n (log n)^(1 - s))` gives `O(n (log n)^(1 - t))` for `t ≤ s`. -/
theorem isBigO_saving_mono {f : ℕ → ℝ} {s t : ℝ} (hts : t ≤ s)
    (h : f =O[atTop] fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - s)) :
    f =O[atTop] fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - t) := by
  refine h.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop 3] with n hn
  show ‖(n : ℝ) * (Real.log (n : ℝ)) ^ (1 - s)‖ ≤ 1 * ‖(n : ℝ) * (Real.log (n : ℝ)) ^ (1 - t)‖
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.log (n : ℝ) :=
    (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_three])
  have h0 : (0 : ℝ) ≤ n := by linarith
  have hs : 0 ≤ (Real.log (n : ℝ)) ^ (1 - s) := Real.rpow_nonneg (by linarith) _
  have ht : 0 ≤ (Real.log (n : ℝ)) ^ (1 - t) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg (mul_nonneg h0 hs), Real.norm_of_nonneg (mul_nonneg h0 ht), one_mul]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog (by linarith)) h0

end PiCut
