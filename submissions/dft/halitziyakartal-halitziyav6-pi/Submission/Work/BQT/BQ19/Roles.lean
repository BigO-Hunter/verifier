import Submission.Work.Reframe.SNet
import Submission.Work.P4L.ORoute
import Submission.Work.BQT.Ctrl
-- NOTE: new in my π/1000 entry; Submission.lean's header says what it adds and whom it credits

/-!
# BQ19 (bqt772), roles of one unit

One unit (one gauge copy `g : Γ`) of the query-thinned controller bqt772 on ONE replica:
* main roles `(g, i, t)`: `i : R34` one of `X_j`, `Y_j` (pairs `j < 17`), port `t`;
* fresh helpers `(g, k, q)`: the helper of slot `q` of the FULL call `k < 19`;
* scratch: the provider's copies `(g, c)` (erased by every call) and the thin-query scratch `(g, j, t)`
  (`j < 16`: one zero scratch role per thin query and port; never live, so its output is free).
Full call `k` acts on the pair `(xOf k, yOf k)` (pairs [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), backward iff [False, True, True, False, True, True, False, True, False, False, True, True, False, False, True, False, True, True, False].
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace BQ19
open Binary Matrix Finset RF

noncomputable section

/-- the live roles: main `(g, i, t)` and fresh helpers `(g, k, q)`. -/
abbrev PLive (Γ T Sl : Type) := (Γ × (R34 × T)) ⊕ (Γ × (Fin 19 × Sl))

/-- the scratch roles: the provider's copies and the thin-query scratch. -/
abbrev PScr (Γ T C : Type) := (Γ × C) ⊕ (Γ × (Fin 16 × T))

/-- all roles. -/
abbrev PRole (Γ T Sl C : Type) := PLive Γ T Sl ⊕ PScr Γ T C

/-- explicit decidable equality (the nested sum is beyond the default instance-search size). -/
instance instDecEqPLive {Γ T Sl : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq Sl] :
    DecidableEq (PLive Γ T Sl) := inferInstanceAs (DecidableEq ((Γ × (R34 × T)) ⊕ (Γ × (Fin 19 × Sl))))
instance instDecEqPScr {Γ T C : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq C] :
    DecidableEq (PScr Γ T C) := inferInstanceAs (DecidableEq ((Γ × C) ⊕ (Γ × (Fin 16 × T))))
instance instDecEqPRole {Γ T Sl C : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq Sl] [DecidableEq C] :
    DecidableEq (PRole Γ T Sl C) := @instDecidableEqSum (PLive Γ T Sl) (PScr Γ T C) instDecEqPLive instDecEqPScr

section Roles
variable {Γ T Sl C : Type}

def mainR (g : Γ) (i : R34) (t : T) : PRole Γ T Sl C := Sum.inl (Sum.inl (g, (i, t)))
def freshR (g : Γ) (k : Fin 19) (q : Sl) : PRole Γ T Sl C := Sum.inl (Sum.inr (g, (k, q)))
def copyR (g : Γ) (c : C) : PRole Γ T Sl C := Sum.inr (Sum.inl (g, c))
def zR (g : Γ) (j : Fin 16) (t : T) : PRole Γ T Sl C := Sum.inr (Sum.inr (g, (j, t)))

/-- the X role of the pair of full call `k`. -/
def xOf (k : Fin 19) : R34 :=
  match k.val with
  | 0 => .x0
  | 1 => .x0
  | 2 => .x0
  | 3 => .x0
  | 4 => .x0
  | 5 => .x0
  | 6 => .x0
  | 7 => .x0
  | 8 => .x0
  | 9 => .x0
  | 10 => .x0
  | 11 => .x0
  | 12 => .x0
  | 13 => .x0
  | 14 => .x0
  | 15 => .x0
  | 16 => .x0
  | 17 => .x0
  | _ => .x0

/-- the Y role of the pair of full call `k`. -/
def yOf (k : Fin 19) : R34 :=
  match k.val with
  | 0 => .y0
  | 1 => .y0
  | 2 => .y0
  | 3 => .y0
  | 4 => .y0
  | 5 => .y0
  | 6 => .y0
  | 7 => .y0
  | 8 => .y0
  | 9 => .y0
  | 10 => .y0
  | 11 => .y0
  | 12 => .y0
  | 13 => .y0
  | 14 => .y0
  | 15 => .y0
  | 16 => .y0
  | 17 => .y0
  | _ => .y0

lemma xOf_ne_yOf (k : Fin 19) : xOf k ≠ yOf k := by
  fin_cases k <;> decide

/-- the roles of the provider's stage, placed on the network at full call `k`. -/
def embF (k : Fin 19) : SRole Γ T Sl C → PRole Γ T Sl C
  | .inl (.inl (.inl (g, t))) => mainR g (xOf k) t
  | .inl (.inl (.inr (g, t))) => mainR g (yOf k) t
  | .inl (.inr (g, q)) => freshR g k q
  | .inr (g, c) => copyR g c

lemma embF_inj (k : Fin 19) : Function.Injective (embF (Γ := Γ) (T := T) (Sl := Sl) (C := C) k) := by
  intro a b h
  have hxy := xOf_ne_yOf k
  rcases a with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩) <;>
    rcases b with (((⟨g', t'⟩ | ⟨g', t'⟩) | ⟨g', q'⟩) | ⟨g', c'⟩) <;>
    simp_all [embF, mainR, freshR, copyR]

def emb (k : Fin 19) : SRole Γ T Sl C ↪ PRole Γ T Sl C := ⟨embF k, embF_inj k⟩

@[simp] lemma emb_X (k : Fin 19) (g : Γ) (t : T) :
    emb (Sl := Sl) (C := C) k (jX (g, t)) = mainR g (xOf k) t := rfl
@[simp] lemma emb_Y (k : Fin 19) (g : Γ) (t : T) :
    emb (Sl := Sl) (C := C) k (jY (g, t)) = mainR g (yOf k) t := rfl
@[simp] lemma emb_S (k : Fin 19) (g : Γ) (q : Sl) :
    emb (T := T) (C := C) k (jS (g, q)) = freshR g k q := rfl
@[simp] lemma emb_C (k : Fin 19) (g : Γ) (c : C) :
    emb (T := T) (Sl := Sl) k (jC (g, c)) = copyR g c := rfl

variable [Fintype Γ] [Fintype T] [Fintype Sl] [Fintype C]

/-- the roles the full call `k` covers: the acting pair, the helpers of call `k`, the copies. -/
lemma covered_emb (k : Fin 19) (r : PRole Γ T Sl C) :
    r ∈ covered (emb (Γ := Γ) (T := T) (Sl := Sl) (C := C) k) ↔
      (∃ g t, r = mainR g (xOf k) t) ∨ (∃ g t, r = mainR g (yOf k) t) ∨ (∃ g q, r = freshR g k q) ∨
        (∃ g c, r = copyR g c) := by
  rw [cover_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩)
    · exact Or.inl ⟨g, t, rfl⟩
    · exact Or.inr (Or.inl ⟨g, t, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨g, q, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨g, c, rfl⟩))
  · rintro (⟨g, t, rfl⟩ | ⟨g, t, rfl⟩ | ⟨g, q, rfl⟩ | ⟨g, c, rfl⟩)
    · exact ⟨jX (g, t), rfl⟩
    · exact ⟨jY (g, t), rfl⟩
    · exact ⟨jS (g, q), rfl⟩
    · exact ⟨jC (g, c), rfl⟩

end Roles

end
end BQ19
end PowerSaving
end OAI

