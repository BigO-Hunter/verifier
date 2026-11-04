import challenges.«van-der-waerden».Statement

/-! The Big O Speedrun QuantitativeVanDerWaerden target.

Target adapter by darkhipo / MultiAgency swarm; Apache-2.0. OpenAI's frozen
statement (`Statement.lean`, upstream text kept whole) proves the constant
`1/100000`. This file re-states the same claim with that constant replaced by a
free rational parameter `c`, the parameterization that lets the verifier
substitute a submitted exact rational and score it. `W r k` is the van der
Waerden number (`Statement.lean`), `Nat.log 2 r` is `⌊log₂ r⌋`. -/
namespace BigOSpeedrun.VanDerWaerden

open OAI.QuantitativeVanDerWaerden

/-- Quantitative van der Waerden lower bound at exponent constant `c`:
for all sufficiently large `k`, uniformly over every color count `r ≥ 2`,

    k ^ (c · k · ⌊log₂ r⌋)  <  W r k.

A **larger** `c` is better (a stronger lower bound on the van der Waerden
number). The bound is attained: the form takes a specific rational `p/q`, not a
strict frontier. `1/8` is the strict, unattained frontier of the method; the
admitted values are the attained `c` below it. -/
def Bound (c : ℚ) : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
    (k : ℝ) ^ ((c : ℝ) * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ)

end BigOSpeedrun.VanDerWaerden
