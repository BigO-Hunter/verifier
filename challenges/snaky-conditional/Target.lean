import challenges.«snaky-conditional».Statement

/-! The Big O Speedrun SnakyConditional target, not a proof of a move bound.
Target adapter by darkhipo; Apache-2.0. OpenAI's fixed N = 35 statement
(`Statement.lean`, frozen upstream text) is kept whole; this file states the
same claim with 35 replaced by `n` and 34 by `n - 1`, the parameterization
that `challenges/other-snaky/Statement.lean` applies to SnakyTwentyOne. -/
namespace BigOSpeedrun.SnakyConditional
open OAI.SnakyConditional OAI.SnakyConditional.OrdinaryStrategy

/-- Maker forces a Snaky within `n` own claims, winning claim included.
Smaller natural bounds are better; no finite board envelope is imposed. -/
def Bound (n : ℕ) : Prop :=
  ∃ σ : Policy Cell,
    (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
    ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ n β ∅ ∅ →
      HasSnaky (playState σ n β ∅ ∅ n).1 ∧
      (playState σ n β ∅ ∅ n).1.card = n ∧
      Disjoint (playState σ n β ∅ ∅ n).1 (playState σ n β ∅ ∅ (n - 1)).2 ∧
      ∀ k, k < n →
        Disjoint (playState σ n β ∅ ∅ k).1 (playState σ n β ∅ ∅ k).2 ∧
        (playState σ n β ∅ ∅ k).2.card = k

end BigOSpeedrun.SnakyConditional
