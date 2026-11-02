import VerifierStatement
import Mathlib

/-!
# Validation of `VerifierStatement.lean` (not part of the trusted target)

No Snaky bound has a proof here. These checks show that the target has the intended shape:

* `card_snaky`, `six_le_card_of_hasSnaky`: the Snaky has six cells in every orientation and
  translation, so a win needs at least six Maker claims.
* `freshPolicy_fresh`: the freshness condition on the policy can be met on the infinite board.
* `card_maker_of_fresh`: freshness forces `card = n`, so that conjunct excludes no winning policy.
* `reply_legal`: against every policy there is a legal Breaker, so the hypothesis
  `LegalRepliesBeforeFinal` is never empty and a false `Bound n` cannot hold vacuously.
* `not_bound_of_lt_six`, `not_bound_zero`: `Bound n` is false for `n < 6`.
* `bound_succ`, `bound_mono`: `Bound n` gives `Bound m` for `n ≤ m`. A smaller `n` is stronger,
  and a policy that wins early can keep claiming fresh cells up to the nominated bound.
* `bound_twentyOne_iff`: `Bound 21` is OpenAI's 21-move statement, word for word.
-/

namespace BigOSpeedrun.Snaky

open OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy

theorem card_snaky : snaky.card = 6 := by decide

theorem orient_injective (r : Fin 8) : Function.Injective (orient r) := by
  rintro ⟨p1, p2⟩ ⟨q1, q2⟩ h
  unfold orient at h
  split at h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h <;>
    simp only [Prod.mk.injEq] <;> omega

theorem placement_injective (r : Fin 8) (t : Cell) : Function.Injective (placement r t) :=
  fun _ _ h => orient_injective r (add_right_cancel h)

theorem six_le_card_of_hasSnaky {M : Finset Cell} (h : HasSnaky M) : 6 ≤ M.card := by
  obtain ⟨r, t, ht⟩ := h
  have hle := Finset.card_le_card ht
  rw [Finset.card_image_of_injective _ (placement_injective r t), card_snaky] at hle
  exact hle

/-- A cell to the right of every cell of `S`. -/
def fresh (S : Finset Cell) : Cell := (((S.sup fun p => p.1.natAbs) + 1 : ℕ), 0)

theorem fresh_not_mem (S : Finset Cell) : fresh S ∉ S := by
  intro h
  have hle := Finset.le_sup (f := fun p : Cell => p.1.natAbs) h
  simp only [fresh, Int.natAbs_natCast] at hle
  omega

/-- A policy that always claims a cell to the right of all claimed cells. -/
def freshPolicy : Policy Cell := fun _ M B => fresh (M ∪ B)

theorem freshPolicy_fresh : ∀ r M B, freshPolicy r M B ∉ M ∧ freshPolicy r M B ∉ B := by
  intro r M B
  have h := fresh_not_mem (M ∪ B)
  simp only [Finset.mem_union, not_or] at h
  exact h

/-- With a fresh policy, Maker has exactly `k` cells after `k` moves, against every Breaker. So the
conjunct `card = n` of `Bound n` is forced by freshness and excludes no winning policy. -/
theorem card_maker_of_fresh {σ : Policy Cell} (hσ : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (β : ℕ → Cell) : ∀ k, (playState σ N β ∅ ∅ k).1.card = k
  | 0 => rfl
  | k + 1 => by
      rw [playState]
      dsimp only
      rw [Finset.card_insert_of_notMem (hσ _ _ _).1, card_maker_of_fresh hσ N β k]

/-- The play against a Breaker who answers with a cell to the right of all claimed cells. -/
def replyState (σ : Policy Cell) (N : ℕ) : ℕ → Finset Cell × Finset Cell
  | 0 => (∅, ∅)
  | k + 1 =>
      let s := replyState σ N k
      let m := σ (N - k) s.1 s.2
      (insert m s.1, insert (fresh (insert m s.1 ∪ s.2)) s.2)

/-- That Breaker, as a sequence of replies. -/
def reply (σ : Policy Cell) (N : ℕ) (k : ℕ) : Cell :=
  fresh (insert (σ (N - k) (replyState σ N k).1 (replyState σ N k).2) (replyState σ N k).1 ∪
    (replyState σ N k).2)

theorem playState_reply (σ : Policy Cell) (N : ℕ) :
    ∀ k, playState σ N (reply σ N) ∅ ∅ k = replyState σ N k
  | 0 => rfl
  | k + 1 => by
      rw [playState, playState_reply σ N k]
      rfl

theorem reply_legal (σ : Policy Cell) (N : ℕ) : LegalRepliesBeforeFinal σ N (reply σ N) ∅ ∅ := by
  intro k _
  have h := fresh_not_mem (insert (σ (N - k) (replyState σ N k).1 (replyState σ N k).2)
    (replyState σ N k).1 ∪ (replyState σ N k).2)
  simp only [Finset.mem_union, not_or] at h
  simp only [makerAt, playState_reply]
  exact h

theorem not_bound_of_lt_six {n : ℕ} (hn : n < 6) : ¬ Bound n := by
  rintro ⟨σ, -, hσ⟩
  obtain ⟨hw, hc, -⟩ := hσ _ (reply_legal σ n)
  have := six_le_card_of_hasSnaky hw
  omega

theorem not_bound_zero : ¬ Bound 0 := not_bound_of_lt_six (by norm_num)

/-- The policy for `n + 1` moves: the moves of `σ` for `n` moves, then a fresh cell. -/
def extend (σ : Policy Cell) : Policy Cell :=
  fun r M B => if r = 1 then fresh (M ∪ B) else σ (r - 1) M B

theorem extend_fresh {σ : Policy Cell} (hσ : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) :
    ∀ r M B, extend σ r M B ∉ M ∧ extend σ r M B ∉ B := by
  intro r M B
  unfold extend
  split
  · exact freshPolicy_fresh r M B
  · exact hσ (r - 1) M B

theorem playState_extend (σ : Policy Cell) (n : ℕ) (β : ℕ → Cell) :
    ∀ k, k ≤ n → playState (extend σ) (n + 1) β ∅ ∅ k = playState σ n β ∅ ∅ k
  | 0, _ => rfl
  | k + 1, hk => by
      have hr : extend σ (n + 1 - k) = σ (n - k) := by
        funext M B
        have h1 : n + 1 - k ≠ 1 := by omega
        have h2 : n + 1 - k - 1 = n - k := by omega
        simp only [extend, h1, ↓reduceIte, h2]
      rw [playState, playState, playState_extend σ n β k (by omega), hr]

theorem makerAt_extend (σ : Policy Cell) (n : ℕ) (β : ℕ → Cell) {k : ℕ} (hk : k < n) :
    makerAt (extend σ) (n + 1) β ∅ ∅ k = makerAt σ n β ∅ ∅ k := by
  have h1 : n + 1 - k ≠ 1 := by omega
  have h2 : n + 1 - k - 1 = n - k := by omega
  simp only [makerAt, playState_extend σ n β k hk.le, extend, h1, ↓reduceIte, h2]

theorem bound_succ {n : ℕ} (h : Bound n) : Bound (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd h not_bound_zero
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  obtain ⟨σ, hfresh, hσ⟩ := h
  refine ⟨extend σ, extend_fresh hfresh, fun β hβ => ?_⟩
  -- A legal Breaker of the longer game is legal in the game of `j + 1` moves.
  have hβn : LegalRepliesBeforeFinal σ (j + 1) β ∅ ∅ := by
    intro k hk
    have := hβ k (by omega)
    rwa [makerAt_extend σ (j + 1) β (by omega), playState_extend σ (j + 1) β k (by omega)] at this
  obtain ⟨hw, hc, -, hk⟩ := hσ β hβn
  obtain ⟨hk1, hk2⟩ := hk j (by omega)
  -- Breaker's reply `j` comes after Maker's last move of the shorter game; it is legal here.
  have hleg := hβ j (by omega)
  rw [makerAt_extend σ (j + 1) β (by omega), playState_extend σ (j + 1) β j (by omega)] at hleg
  have hstep : playState σ (j + 1) β ∅ ∅ (j + 1) =
      (insert (makerAt σ (j + 1) β ∅ ∅ j) (playState σ (j + 1) β ∅ ∅ j).1,
        insert (β j) (playState σ (j + 1) β ∅ ∅ j).2) := by
    rw [playState]
    rfl
  have hmB : makerAt σ (j + 1) β ∅ ∅ j ∉ (playState σ (j + 1) β ∅ ∅ j).2 := by
    simp only [makerAt]
    exact (hfresh _ _ _).2
  have hMB : Disjoint (playState σ (j + 1) β ∅ ∅ (j + 1)).1 (playState σ (j + 1) β ∅ ∅ (j + 1)).2 := by
    rw [hstep]
    dsimp only
    rw [Finset.disjoint_insert_right, Finset.disjoint_insert_left]
    exact ⟨hleg.1, hmB, hk1⟩
  have hBcard : (playState σ (j + 1) β ∅ ∅ (j + 1)).2.card = j + 1 := by
    rw [hstep]
    dsimp only
    rw [Finset.card_insert_of_notMem hleg.2, hk2]
  -- The extended policy's last move is a fresh cell.
  have hlast : playState (extend σ) (j + 1 + 1) β ∅ ∅ (j + 1 + 1) =
      (insert (fresh ((playState σ (j + 1) β ∅ ∅ (j + 1)).1 ∪ (playState σ (j + 1) β ∅ ∅ (j + 1)).2))
          (playState σ (j + 1) β ∅ ∅ (j + 1)).1,
        insert (β (j + 1)) (playState σ (j + 1) β ∅ ∅ (j + 1)).2) := by
    rw [playState, playState_extend σ (j + 1) β (j + 1) le_rfl]
    simp [extend]
  have hprev : playState (extend σ) (j + 1 + 1) β ∅ ∅ (j + 1 + 1 - 1) =
      playState σ (j + 1) β ∅ ∅ (j + 1) := by
    rw [Nat.add_sub_cancel]
    exact playState_extend σ (j + 1) β (j + 1) le_rfl
  have hf := freshPolicy_fresh 0 (playState σ (j + 1) β ∅ ∅ (j + 1)).1 (playState σ (j + 1) β ∅ ∅ (j + 1)).2
  have hfM : fresh ((playState σ (j + 1) β ∅ ∅ (j + 1)).1 ∪ (playState σ (j + 1) β ∅ ∅ (j + 1)).2) ∉
      (playState σ (j + 1) β ∅ ∅ (j + 1)).1 := hf.1
  have hfB : fresh ((playState σ (j + 1) β ∅ ∅ (j + 1)).1 ∪ (playState σ (j + 1) β ∅ ∅ (j + 1)).2) ∉
      (playState σ (j + 1) β ∅ ∅ (j + 1)).2 := hf.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlast]
    obtain ⟨r, t, ht⟩ := hw
    exact ⟨r, t, ht.trans (Finset.subset_insert _ _)⟩
  · rw [hlast]
    dsimp only
    rw [Finset.card_insert_of_notMem hfM, hc]
  · rw [hlast, hprev]
    dsimp only
    exact Finset.disjoint_insert_left.2 ⟨hfB, hMB⟩
  · intro k hkn
    rcases Nat.lt_or_ge k (j + 1) with hk' | hk'
    · rw [playState_extend σ (j + 1) β k hk'.le]
      exact hk k hk'
    · obtain rfl : k = j + 1 := by omega
      rw [playState_extend σ (j + 1) β (j + 1) le_rfl]
      exact ⟨hMB, hBcard⟩

theorem bound_mono {n m : ℕ} (h : Bound n) (hnm : n ≤ m) : Bound m := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact bound_succ ih

theorem bound_twentyOne_iff :
    Bound 21 ↔ ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 21 β ∅ ∅ →
        HasSnaky (playState σ 21 β ∅ ∅ 21).1 ∧
        (playState σ 21 β ∅ ∅ 21).1.card = 21 ∧
        Disjoint (playState σ 21 β ∅ ∅ 21).1 (playState σ 21 β ∅ ∅ 20).2 ∧
        ∀ k, k < 21 →
          Disjoint (playState σ 21 β ∅ ∅ k).1 (playState σ 21 β ∅ ∅ k).2 ∧
          (playState σ 21 β ∅ ∅ k).2.card = k :=
  Iff.rfl

end BigOSpeedrun.Snaky

#print axioms BigOSpeedrun.Snaky.not_bound_of_lt_six
#print axioms BigOSpeedrun.Snaky.freshPolicy_fresh
#print axioms BigOSpeedrun.Snaky.card_maker_of_fresh
#print axioms BigOSpeedrun.Snaky.reply_legal
#print axioms BigOSpeedrun.Snaky.bound_mono
#print axioms BigOSpeedrun.Snaky.bound_twentyOne_iff
