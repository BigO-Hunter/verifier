import Statement
import Mathlib.NumberTheory.PrimeCounting

/-!
# Validation of `Statement.lean` (not part of the trusted target)

* `bound_mono`: `Bound B` gives `Bound B'` for `B ≤ B'` (smaller is better).
* `nth_prime_strictMono`, `nth_prime_prime`: `Nat.nth Nat.Prime` lists the primes in order.
* `not_bound_one`: no bound below `2` holds, so `Bound 2` is the twin prime conjecture and the
  natural subtraction never hides a negative gap.
* `bound_iff_primes`: `Bound B` holds exactly when for every `n₀` there are primes
  `n₀ ≤ p < q ≤ p + B` (the form of Axiom Math's `bombieriVinogradov_implies_prime_gap_le_246`).
-/

namespace BigOSpeedrun.PrimeGaps

open Filter

theorem nth_prime_strictMono : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem nth_prime_prime (n : ℕ) : (Nat.nth Nat.Prime n).Prime :=
  Nat.prime_nth_prime n

theorem bound_mono {B B' : ℕ} (h : Bound B) (hB : B ≤ B') : Bound B' :=
  h.mono fun _ hm => le_trans hm hB

/-- For `m ≥ 1` both primes are odd, so their gap is at least `2`. -/
theorem two_le_gap {m : ℕ} (hm : 1 ≤ m) :
    2 ≤ Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m := by
  have hlt : Nat.nth Nat.Prime m < Nat.nth Nat.Prime (m + 1) := nth_prime_strictMono (by omega)
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have ha : 2 < Nat.nth Nat.Prime m := h0 ▸ nth_prime_strictMono (by omega)
  have hb : 2 < Nat.nth Nat.Prime (m + 1) := h0 ▸ nth_prime_strictMono (by omega)
  obtain ⟨a, ha'⟩ := (nth_prime_prime m).odd_of_ne_two ha.ne'
  obtain ⟨b, hb'⟩ := (nth_prime_prime (m + 1)).odd_of_ne_two hb.ne'
  omega

theorem not_bound_one : ¬ Bound 1 := by
  intro h
  obtain ⟨m, hm, hgap⟩ := Filter.frequently_atTop.1 h 1
  have := two_le_gap hm
  omega

theorem not_bound_lt_two {B : ℕ} (hB : B < 2) : ¬ Bound B :=
  fun h => not_bound_one (bound_mono h (by omega))

theorem bound_iff_primes (B : ℕ) :
    Bound B ↔ ∀ n₀ : ℕ, ∃ p q : ℕ, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + B := by
  constructor
  · intro h n₀
    obtain ⟨m, hm, hgap⟩ := Filter.frequently_atTop.1 h n₀
    have hlt : Nat.nth Nat.Prime m < Nat.nth Nat.Prime (m + 1) := nth_prime_strictMono (by omega)
    have hle : m ≤ Nat.nth Nat.Prime m := nth_prime_strictMono.id_le m
    exact ⟨_, _, le_trans hm hle, hlt, nth_prime_prime m, nth_prime_prime (m + 1), by omega⟩
  · intro h
    refine Filter.frequently_atTop.2 fun a => ?_
    obtain ⟨p, q, hp0, hpq, hp, hq, hqB⟩ := h (Nat.nth Nat.Prime a)
    have hpk : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
    have hqk : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
    -- p ≥ nth a, so the index of p is at least a
    have hka : a ≤ Nat.count Nat.Prime p := by
      by_contra hc
      have := nth_prime_strictMono (not_le.1 hc)
      omega
    -- q > p is prime, so the next prime after p is at most q
    have hkq : Nat.count Nat.Prime p + 1 ≤ Nat.count Nat.Prime q := by
      by_contra hc
      have := nth_prime_strictMono.monotone (show Nat.count Nat.Prime q ≤ Nat.count Nat.Prime p by omega)
      omega
    have hnext := nth_prime_strictMono.monotone hkq
    refine ⟨Nat.count Nat.Prime p, hka, ?_⟩
    omega

end BigOSpeedrun.PrimeGaps

#print axioms BigOSpeedrun.PrimeGaps.not_bound_one
#print axioms BigOSpeedrun.PrimeGaps.bound_iff_primes
