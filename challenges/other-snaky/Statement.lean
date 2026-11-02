import challenges.«other-snaky».Model

/-! The Big O Speedrun Snaky target, not a proof of a Snaky move bound.
New parameterization by fluorine with Codex (verifier PR #65); Apache-2.0.
OpenAI's 21-move statement is kept whole, with 21 replaced by n and 20 by n - 1. -/
namespace BigOSpeedrun.Snaky
open OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy

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

end BigOSpeedrun.Snaky
