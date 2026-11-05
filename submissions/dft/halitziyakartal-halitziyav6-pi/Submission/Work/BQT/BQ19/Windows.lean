import Submission.Work.P4L.Windows
import Submission.Work.BQT.G19.Lemmas
import Submission.Work.BQT.BQ19.View
-- NOTE: new in my π/1000 entry; Submission.lean's header says what it adds and whom it credits

/-!
# BQ19 (bqt772), the retained idle windows (raw: ONE block of rank 8 m per owner)

Windows (pair, stages a..b of the full calls): [(1, 0, 3), (2, 0, 1), (3, 2, 3), (4, 4, 10), (5, 4, 6), (6, 5, 6), (7, 7, 10), (8, 7, 8), (9, 9, 10), (10, 11, 18), (11, 11, 14), (12, 11, 12), (13, 13, 14), (14, 15, 18), (15, 15, 16), (16, 17, 18)].  Every owner climbs the whole window with ONE block of
rank `8 m` inside `BBC (base t) l g` (`BC.reach_of_pos`, `BC.reach_of_lt`); the window is one operator route
(`ORoute.steps_inv`) and moves the view of every port by `win x y m`, `m` the product of its stage transforms.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace OAI
namespace PowerSaving
namespace BQ19
open Binary Matrix Finset RAM SS CB RF BC GX GF

noncomputable section

section Win
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
  [Fintype C] [DecidableEq C] (base : T → OBase H) (l : H) (hH : Fintype.card H = 9)

/-- the two owner roles of a pair at every port. -/
def ownerSet (x y : R34) : Finset (PRole (Orth (LC (Fin 18) H l)) T Sl C) :=
  (Finset.univ : Finset (Orth (LC (Fin 18) H l) × T)).image (fun p => mainR p.1 x p.2) ∪
    (Finset.univ : Finset (Orth (LC (Fin 18) H l) × T)).image (fun p => mainR p.1 y p.2)

lemma mem_ownerSet (x y : R34) (g : Orth (LC (Fin 18) H l)) (i : R34) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l x y ↔ (i = x ∨ i = y) := by
  unfold ownerSet
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨⟨g', t'⟩, -, h⟩ | ⟨⟨g', t'⟩, -, h⟩)
    · simp only [mainR, Sum.inl.injEq, Prod.mk.injEq] at h; exact Or.inl h.2.1.symm
    · simp only [mainR, Sum.inl.injEq, Prod.mk.injEq] at h; exact Or.inr h.2.1.symm
  · rintro (rfl | rfl)
    · exact Or.inl ⟨(g, t), Finset.mem_univ _, rfl⟩
    · exact Or.inr ⟨(g, t), Finset.mem_univ _, rfl⟩

lemma ownerSet_main (x y : R34) (r : PRole (Orth (LC (Fin 18) H l)) T Sl C)
    (hr : r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l x y) : ∃ g i t, r = mainR g i t := by
  unfold ownerSet at hr
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hr
  rcases hr with (⟨⟨g, t⟩, -, rfl⟩ | ⟨⟨g, t⟩, -, rfl⟩)
  · exact ⟨g, x, t, rfl⟩
  · exact ⟨g, y, t, rfl⟩

/-- start / end frames of a window's owners. -/
def winF (x : R34) (a : ℕ) : PRole (Orth (LC (Fin 18) H l)) T Sl C → CMat (LC (Fin 18) H l)
  | .inl (.inl (g, (i, t))) =>
      if i = x then frame (BBC (base t) l g) (G19.setX l a) else frame (BBC (base t) l g) (G19.setY l a)
  | _ => 1

def winF' (x : R34) (a : ℕ) : PRole (Orth (LC (Fin 18) H l)) T Sl C → CMat (LC (Fin 18) H l)
  | .inl (.inl (g, (i, t))) =>
      if i = x then unframe (BBC (base t) l g) (G19.setX l a) else unframe (BBC (base t) l g) (G19.setY l a)
  | _ => 1

lemma winF_inv (x : R34) (a : ℕ) (r : PRole (Orth (LC (Fin 18) H l)) T Sl C) :
    winF (Sl := Sl) (C := C) base l x a r * winF' (Sl := Sl) (C := C) base l x a r = 1 := by
  rcases r with ((⟨g, i, t⟩ | h) | c)
  · simp only [winF, winF']; split_ifs <;> exact unframe_right _ _
  · simp [winF, winF']
  · simp [winF, winF']

include hH in
lemma win0X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 0)) (frame (BBC (base t) l g) (G19.setX l 4))
      (fun φ => bcost φ 32) := by
  have h1 := G19.card_setX l hH 0 (by norm_num)
  have h2 := G19.card_setX l hH 4 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 0 4 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
lemma win0Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 0)) (frame (BBC (base t) l g) (G19.setY l 4))
      (fun φ => bcost φ 32) := by
  have h1 := G19.card_setY l hH 0 (by norm_num)
  have h2 := G19.card_setY l hH 4 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 0 4 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
/-- **window 0** (pair 1, stages 0..3) as an operator route (all gauges and ports). -/
theorem winSeg0 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x1 .y1
      then matAct f (winF (Sl := Sl) (C := C) base l .x1 4 r * winF' (Sl := Sl) (C := C) base l .x1 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x1 .y1, bcost φ 32) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x1 0) (winF' base l .x1 0) (winF base l .x1 4)
    (fun r _ => winF_inv base l .x1 0 r) (fun _ φ => bcost φ 32) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x1 .y1 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win0X base l hH t g _ (mainR g .x1 t)
  · exact win0Y base l hH t g _ (mainR g .y1 t)

/-- window 0 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg0 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x1 .y1
      then matAct f (winF (Sl := Sl) (C := C) base l .x1 4 r * winF' (Sl := Sl) (C := C) base l .x1 0 r) (y r)
      else y r)
      = win .x1 .y1 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 4).biUnion fun j => G19.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 0 3 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 0 3 (by norm_num)
  apply view_steps_win _ _ f y g t .x1 .y1 (by decide) _ (fun i => mem_ownerSet l .x1 .y1 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 4 = G19.setX l 0 ∪ ((Finset.range 4).biUnion fun j => G19.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y1 ≠ R34.x1)]
    rw [← matAct_mul]
    have e : G19.setY l 4 = G19.setY l 0 ∪ ((Finset.range 4).biUnion fun j => G19.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win1X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 0)) (frame (BBC (base t) l g) (G19.setX l 2))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setX l hH 0 (by norm_num)
  have h2 := G19.card_setX l hH 2 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 0 2 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win1Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 0)) (frame (BBC (base t) l g) (G19.setY l 2))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setY l hH 0 (by norm_num)
  have h2 := G19.card_setY l hH 2 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 0 2 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 1** (pair 2, stages 0..1) as an operator route (all gauges and ports). -/
theorem winSeg1 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x2 .y2
      then matAct f (winF (Sl := Sl) (C := C) base l .x2 2 r * winF' (Sl := Sl) (C := C) base l .x2 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x2 .y2, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x2 0) (winF' base l .x2 0) (winF base l .x2 2)
    (fun r _ => winF_inv base l .x2 0 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x2 .y2 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win1X base l hH t g _ (mainR g .x2 t)
  · exact win1Y base l hH t g _ (mainR g .y2 t)

/-- window 1 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg1 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x2 .y2
      then matAct f (winF (Sl := Sl) (C := C) base l .x2 2 r * winF' (Sl := Sl) (C := C) base l .x2 0 r) (y r)
      else y r)
      = win .x2 .y2 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G19.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 0 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 0 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x2 .y2 (by decide) _ (fun i => mem_ownerSet l .x2 .y2 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 2 = G19.setX l 0 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y2 ≠ R34.x2)]
    rw [← matAct_mul]
    have e : G19.setY l 2 = G19.setY l 0 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win2X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 2)) (frame (BBC (base t) l g) (G19.setX l 4))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setX l hH 2 (by norm_num)
  have h2 := G19.card_setX l hH 4 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 2 4 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win2Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 2)) (frame (BBC (base t) l g) (G19.setY l 4))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setY l hH 2 (by norm_num)
  have h2 := G19.card_setY l hH 4 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 2 4 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 2** (pair 3, stages 2..3) as an operator route (all gauges and ports). -/
theorem winSeg2 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x3 .y3
      then matAct f (winF (Sl := Sl) (C := C) base l .x3 4 r * winF' (Sl := Sl) (C := C) base l .x3 2 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x3 .y3, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x3 2) (winF' base l .x3 2) (winF base l .x3 4)
    (fun r _ => winF_inv base l .x3 2 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x3 .y3 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win2X base l hH t g _ (mainR g .x3 t)
  · exact win2Y base l hH t g _ (mainR g .y3 t)

/-- window 2 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg2 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x3 .y3
      then matAct f (winF (Sl := Sl) (C := C) base l .x3 4 r * winF' (Sl := Sl) (C := C) base l .x3 2 r) (y r)
      else y r)
      = win .x3 .y3 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G19.incr l (2 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 2 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 2 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x3 .y3 (by decide) _ (fun i => mem_ownerSet l .x3 .y3 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 4 = G19.setX l 2 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (2 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y3 ≠ R34.x3)]
    rw [← matAct_mul]
    have e : G19.setY l 4 = G19.setY l 2 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (2 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win3X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 4)) (frame (BBC (base t) l g) (G19.setX l 11))
      (fun φ => bcost φ 56) := by
  have h1 := G19.card_setX l hH 4 (by norm_num)
  have h2 := G19.card_setX l hH 11 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 4 11 (by norm_num) (by norm_num))
    56 (by omega) (by omega))

include hH in
lemma win3Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 4)) (frame (BBC (base t) l g) (G19.setY l 11))
      (fun φ => bcost φ 56) := by
  have h1 := G19.card_setY l hH 4 (by norm_num)
  have h2 := G19.card_setY l hH 11 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 4 11 (by norm_num) (by norm_num))
    56 (by omega) (by omega))

include hH in
/-- **window 3** (pair 4, stages 4..10) as an operator route (all gauges and ports). -/
theorem winSeg3 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x4 .y4
      then matAct f (winF (Sl := Sl) (C := C) base l .x4 11 r * winF' (Sl := Sl) (C := C) base l .x4 4 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x4 .y4, bcost φ 56) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x4 4) (winF' base l .x4 4) (winF base l .x4 11)
    (fun r _ => winF_inv base l .x4 4 r) (fun _ φ => bcost φ 56) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x4 .y4 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win3X base l hH t g _ (mainR g .x4 t)
  · exact win3Y base l hH t g _ (mainR g .y4 t)

/-- window 3 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg3 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x4 .y4
      then matAct f (winF (Sl := Sl) (C := C) base l .x4 11 r * winF' (Sl := Sl) (C := C) base l .x4 4 r) (y r)
      else y r)
      = win .x4 .y4 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 7).biUnion fun j => G19.incr l (4 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 4 6 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 4 6 (by norm_num)
  apply view_steps_win _ _ f y g t .x4 .y4 (by decide) _ (fun i => mem_ownerSet l .x4 .y4 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 11 = G19.setX l 4 ∪ ((Finset.range 7).biUnion fun j => G19.incr l (4 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y4 ≠ R34.x4)]
    rw [← matAct_mul]
    have e : G19.setY l 11 = G19.setY l 4 ∪ ((Finset.range 7).biUnion fun j => G19.incr l (4 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win4X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 4)) (frame (BBC (base t) l g) (G19.setX l 7))
      (fun φ => bcost φ 24) := by
  have h1 := G19.card_setX l hH 4 (by norm_num)
  have h2 := G19.card_setX l hH 7 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 4 7 (by norm_num) (by norm_num))
    24 (by omega) (by omega))

include hH in
lemma win4Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 4)) (frame (BBC (base t) l g) (G19.setY l 7))
      (fun φ => bcost φ 24) := by
  have h1 := G19.card_setY l hH 4 (by norm_num)
  have h2 := G19.card_setY l hH 7 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 4 7 (by norm_num) (by norm_num))
    24 (by omega) (by omega))

include hH in
/-- **window 4** (pair 5, stages 4..6) as an operator route (all gauges and ports). -/
theorem winSeg4 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x5 .y5
      then matAct f (winF (Sl := Sl) (C := C) base l .x5 7 r * winF' (Sl := Sl) (C := C) base l .x5 4 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x5 .y5, bcost φ 24) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x5 4) (winF' base l .x5 4) (winF base l .x5 7)
    (fun r _ => winF_inv base l .x5 4 r) (fun _ φ => bcost φ 24) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x5 .y5 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win4X base l hH t g _ (mainR g .x5 t)
  · exact win4Y base l hH t g _ (mainR g .y5 t)

/-- window 4 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg4 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x5 .y5
      then matAct f (winF (Sl := Sl) (C := C) base l .x5 7 r * winF' (Sl := Sl) (C := C) base l .x5 4 r) (y r)
      else y r)
      = win .x5 .y5 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 3).biUnion fun j => G19.incr l (4 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 4 2 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 4 2 (by norm_num)
  apply view_steps_win _ _ f y g t .x5 .y5 (by decide) _ (fun i => mem_ownerSet l .x5 .y5 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 7 = G19.setX l 4 ∪ ((Finset.range 3).biUnion fun j => G19.incr l (4 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y5 ≠ R34.x5)]
    rw [← matAct_mul]
    have e : G19.setY l 7 = G19.setY l 4 ∪ ((Finset.range 3).biUnion fun j => G19.incr l (4 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win5X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 5)) (frame (BBC (base t) l g) (G19.setX l 7))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setX l hH 5 (by norm_num)
  have h2 := G19.card_setX l hH 7 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 5 7 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win5Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 5)) (frame (BBC (base t) l g) (G19.setY l 7))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setY l hH 5 (by norm_num)
  have h2 := G19.card_setY l hH 7 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 5 7 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 5** (pair 6, stages 5..6) as an operator route (all gauges and ports). -/
theorem winSeg5 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x6 .y6
      then matAct f (winF (Sl := Sl) (C := C) base l .x6 7 r * winF' (Sl := Sl) (C := C) base l .x6 5 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x6 .y6, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x6 5) (winF' base l .x6 5) (winF base l .x6 7)
    (fun r _ => winF_inv base l .x6 5 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x6 .y6 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win5X base l hH t g _ (mainR g .x6 t)
  · exact win5Y base l hH t g _ (mainR g .y6 t)

/-- window 5 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg5 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x6 .y6
      then matAct f (winF (Sl := Sl) (C := C) base l .x6 7 r * winF' (Sl := Sl) (C := C) base l .x6 5 r) (y r)
      else y r)
      = win .x6 .y6 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G19.incr l (5 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 5 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 5 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x6 .y6 (by decide) _ (fun i => mem_ownerSet l .x6 .y6 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 7 = G19.setX l 5 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (5 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y6 ≠ R34.x6)]
    rw [← matAct_mul]
    have e : G19.setY l 7 = G19.setY l 5 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (5 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win6X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 7)) (frame (BBC (base t) l g) (G19.setX l 11))
      (fun φ => bcost φ 32) := by
  have h1 := G19.card_setX l hH 7 (by norm_num)
  have h2 := G19.card_setX l hH 11 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 7 11 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
lemma win6Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 7)) (frame (BBC (base t) l g) (G19.setY l 11))
      (fun φ => bcost φ 32) := by
  have h1 := G19.card_setY l hH 7 (by norm_num)
  have h2 := G19.card_setY l hH 11 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 7 11 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
/-- **window 6** (pair 7, stages 7..10) as an operator route (all gauges and ports). -/
theorem winSeg6 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x7 .y7
      then matAct f (winF (Sl := Sl) (C := C) base l .x7 11 r * winF' (Sl := Sl) (C := C) base l .x7 7 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x7 .y7, bcost φ 32) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x7 7) (winF' base l .x7 7) (winF base l .x7 11)
    (fun r _ => winF_inv base l .x7 7 r) (fun _ φ => bcost φ 32) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x7 .y7 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win6X base l hH t g _ (mainR g .x7 t)
  · exact win6Y base l hH t g _ (mainR g .y7 t)

/-- window 6 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg6 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x7 .y7
      then matAct f (winF (Sl := Sl) (C := C) base l .x7 11 r * winF' (Sl := Sl) (C := C) base l .x7 7 r) (y r)
      else y r)
      = win .x7 .y7 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 4).biUnion fun j => G19.incr l (7 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 7 3 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 7 3 (by norm_num)
  apply view_steps_win _ _ f y g t .x7 .y7 (by decide) _ (fun i => mem_ownerSet l .x7 .y7 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 11 = G19.setX l 7 ∪ ((Finset.range 4).biUnion fun j => G19.incr l (7 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y7 ≠ R34.x7)]
    rw [← matAct_mul]
    have e : G19.setY l 11 = G19.setY l 7 ∪ ((Finset.range 4).biUnion fun j => G19.incr l (7 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win7X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 7)) (frame (BBC (base t) l g) (G19.setX l 9))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setX l hH 7 (by norm_num)
  have h2 := G19.card_setX l hH 9 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 7 9 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win7Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 7)) (frame (BBC (base t) l g) (G19.setY l 9))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setY l hH 7 (by norm_num)
  have h2 := G19.card_setY l hH 9 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 7 9 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 7** (pair 8, stages 7..8) as an operator route (all gauges and ports). -/
theorem winSeg7 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x8 .y8
      then matAct f (winF (Sl := Sl) (C := C) base l .x8 9 r * winF' (Sl := Sl) (C := C) base l .x8 7 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x8 .y8, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x8 7) (winF' base l .x8 7) (winF base l .x8 9)
    (fun r _ => winF_inv base l .x8 7 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x8 .y8 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win7X base l hH t g _ (mainR g .x8 t)
  · exact win7Y base l hH t g _ (mainR g .y8 t)

/-- window 7 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg7 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x8 .y8
      then matAct f (winF (Sl := Sl) (C := C) base l .x8 9 r * winF' (Sl := Sl) (C := C) base l .x8 7 r) (y r)
      else y r)
      = win .x8 .y8 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G19.incr l (7 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 7 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 7 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x8 .y8 (by decide) _ (fun i => mem_ownerSet l .x8 .y8 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 9 = G19.setX l 7 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (7 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y8 ≠ R34.x8)]
    rw [← matAct_mul]
    have e : G19.setY l 9 = G19.setY l 7 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (7 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win8X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 9)) (frame (BBC (base t) l g) (G19.setX l 11))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setX l hH 9 (by norm_num)
  have h2 := G19.card_setX l hH 11 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 9 11 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win8Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 9)) (frame (BBC (base t) l g) (G19.setY l 11))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setY l hH 9 (by norm_num)
  have h2 := G19.card_setY l hH 11 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 9 11 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 8** (pair 9, stages 9..10) as an operator route (all gauges and ports). -/
theorem winSeg8 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x9 .y9
      then matAct f (winF (Sl := Sl) (C := C) base l .x9 11 r * winF' (Sl := Sl) (C := C) base l .x9 9 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x9 .y9, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x9 9) (winF' base l .x9 9) (winF base l .x9 11)
    (fun r _ => winF_inv base l .x9 9 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x9 .y9 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win8X base l hH t g _ (mainR g .x9 t)
  · exact win8Y base l hH t g _ (mainR g .y9 t)

/-- window 8 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg8 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x9 .y9
      then matAct f (winF (Sl := Sl) (C := C) base l .x9 11 r * winF' (Sl := Sl) (C := C) base l .x9 9 r) (y r)
      else y r)
      = win .x9 .y9 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G19.incr l (9 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 9 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 9 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x9 .y9 (by decide) _ (fun i => mem_ownerSet l .x9 .y9 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 11 = G19.setX l 9 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (9 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y9 ≠ R34.x9)]
    rw [← matAct_mul]
    have e : G19.setY l 11 = G19.setY l 9 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (9 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win9X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 11)) (frame (BBC (base t) l g) (G19.setX l 19))
      (fun φ => bcost φ 64) := by
  have h1 := G19.card_setX l hH 11 (by norm_num)
  have h2 := G19.card_setX l hH 19 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 11 19 (by norm_num) (by norm_num))
    64 (by omega) (by omega))

include hH in
lemma win9Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 11)) (frame (BBC (base t) l g) (G19.setY l 19))
      (fun φ => bcost φ 64) := by
  have h1 := G19.card_setY l hH 11 (by norm_num)
  have h2 := G19.card_setY l hH 19 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 11 19 (by norm_num) (by norm_num))
    64 (by omega) (by omega))

include hH in
/-- **window 9** (pair 10, stages 11..18) as an operator route (all gauges and ports). -/
theorem winSeg9 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x10 .y10
      then matAct f (winF (Sl := Sl) (C := C) base l .x10 19 r * winF' (Sl := Sl) (C := C) base l .x10 11 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x10 .y10, bcost φ 64) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x10 11) (winF' base l .x10 11) (winF base l .x10 19)
    (fun r _ => winF_inv base l .x10 11 r) (fun _ φ => bcost φ 64) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x10 .y10 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win9X base l hH t g _ (mainR g .x10 t)
  · exact win9Y base l hH t g _ (mainR g .y10 t)

/-- window 9 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg9 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x10 .y10
      then matAct f (winF (Sl := Sl) (C := C) base l .x10 19 r * winF' (Sl := Sl) (C := C) base l .x10 11 r) (y r)
      else y r)
      = win .x10 .y10 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 8).biUnion fun j => G19.incr l (11 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 11 7 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 11 7 (by norm_num)
  apply view_steps_win _ _ f y g t .x10 .y10 (by decide) _ (fun i => mem_ownerSet l .x10 .y10 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 19 = G19.setX l 11 ∪ ((Finset.range 8).biUnion fun j => G19.incr l (11 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y10 ≠ R34.x10)]
    rw [← matAct_mul]
    have e : G19.setY l 19 = G19.setY l 11 ∪ ((Finset.range 8).biUnion fun j => G19.incr l (11 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win10X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 11)) (frame (BBC (base t) l g) (G19.setX l 15))
      (fun φ => bcost φ 32) := by
  have h1 := G19.card_setX l hH 11 (by norm_num)
  have h2 := G19.card_setX l hH 15 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 11 15 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
lemma win10Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 11)) (frame (BBC (base t) l g) (G19.setY l 15))
      (fun φ => bcost φ 32) := by
  have h1 := G19.card_setY l hH 11 (by norm_num)
  have h2 := G19.card_setY l hH 15 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 11 15 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
/-- **window 10** (pair 11, stages 11..14) as an operator route (all gauges and ports). -/
theorem winSeg10 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x11 .y11
      then matAct f (winF (Sl := Sl) (C := C) base l .x11 15 r * winF' (Sl := Sl) (C := C) base l .x11 11 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x11 .y11, bcost φ 32) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x11 11) (winF' base l .x11 11) (winF base l .x11 15)
    (fun r _ => winF_inv base l .x11 11 r) (fun _ φ => bcost φ 32) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x11 .y11 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win10X base l hH t g _ (mainR g .x11 t)
  · exact win10Y base l hH t g _ (mainR g .y11 t)

/-- window 10 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg10 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x11 .y11
      then matAct f (winF (Sl := Sl) (C := C) base l .x11 15 r * winF' (Sl := Sl) (C := C) base l .x11 11 r) (y r)
      else y r)
      = win .x11 .y11 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 4).biUnion fun j => G19.incr l (11 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 11 3 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 11 3 (by norm_num)
  apply view_steps_win _ _ f y g t .x11 .y11 (by decide) _ (fun i => mem_ownerSet l .x11 .y11 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 15 = G19.setX l 11 ∪ ((Finset.range 4).biUnion fun j => G19.incr l (11 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y11 ≠ R34.x11)]
    rw [← matAct_mul]
    have e : G19.setY l 15 = G19.setY l 11 ∪ ((Finset.range 4).biUnion fun j => G19.incr l (11 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win11X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 11)) (frame (BBC (base t) l g) (G19.setX l 13))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setX l hH 11 (by norm_num)
  have h2 := G19.card_setX l hH 13 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 11 13 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win11Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 11)) (frame (BBC (base t) l g) (G19.setY l 13))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setY l hH 11 (by norm_num)
  have h2 := G19.card_setY l hH 13 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 11 13 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 11** (pair 12, stages 11..12) as an operator route (all gauges and ports). -/
theorem winSeg11 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x12 .y12
      then matAct f (winF (Sl := Sl) (C := C) base l .x12 13 r * winF' (Sl := Sl) (C := C) base l .x12 11 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x12 .y12, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x12 11) (winF' base l .x12 11) (winF base l .x12 13)
    (fun r _ => winF_inv base l .x12 11 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x12 .y12 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win11X base l hH t g _ (mainR g .x12 t)
  · exact win11Y base l hH t g _ (mainR g .y12 t)

/-- window 11 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg11 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x12 .y12
      then matAct f (winF (Sl := Sl) (C := C) base l .x12 13 r * winF' (Sl := Sl) (C := C) base l .x12 11 r) (y r)
      else y r)
      = win .x12 .y12 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G19.incr l (11 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 11 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 11 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x12 .y12 (by decide) _ (fun i => mem_ownerSet l .x12 .y12 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 13 = G19.setX l 11 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (11 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y12 ≠ R34.x12)]
    rw [← matAct_mul]
    have e : G19.setY l 13 = G19.setY l 11 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (11 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win12X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 13)) (frame (BBC (base t) l g) (G19.setX l 15))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setX l hH 13 (by norm_num)
  have h2 := G19.card_setX l hH 15 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 13 15 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win12Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 13)) (frame (BBC (base t) l g) (G19.setY l 15))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setY l hH 13 (by norm_num)
  have h2 := G19.card_setY l hH 15 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 13 15 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 12** (pair 13, stages 13..14) as an operator route (all gauges and ports). -/
theorem winSeg12 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x13 .y13
      then matAct f (winF (Sl := Sl) (C := C) base l .x13 15 r * winF' (Sl := Sl) (C := C) base l .x13 13 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x13 .y13, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x13 13) (winF' base l .x13 13) (winF base l .x13 15)
    (fun r _ => winF_inv base l .x13 13 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x13 .y13 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win12X base l hH t g _ (mainR g .x13 t)
  · exact win12Y base l hH t g _ (mainR g .y13 t)

/-- window 12 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg12 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x13 .y13
      then matAct f (winF (Sl := Sl) (C := C) base l .x13 15 r * winF' (Sl := Sl) (C := C) base l .x13 13 r) (y r)
      else y r)
      = win .x13 .y13 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G19.incr l (13 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 13 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 13 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x13 .y13 (by decide) _ (fun i => mem_ownerSet l .x13 .y13 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 15 = G19.setX l 13 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (13 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y13 ≠ R34.x13)]
    rw [← matAct_mul]
    have e : G19.setY l 15 = G19.setY l 13 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (13 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win13X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 15)) (frame (BBC (base t) l g) (G19.setX l 19))
      (fun φ => bcost φ 32) := by
  have h1 := G19.card_setX l hH 15 (by norm_num)
  have h2 := G19.card_setX l hH 19 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 15 19 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
lemma win13Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 15)) (frame (BBC (base t) l g) (G19.setY l 19))
      (fun φ => bcost φ 32) := by
  have h1 := G19.card_setY l hH 15 (by norm_num)
  have h2 := G19.card_setY l hH 19 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 15 19 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
/-- **window 13** (pair 14, stages 15..18) as an operator route (all gauges and ports). -/
theorem winSeg13 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x14 .y14
      then matAct f (winF (Sl := Sl) (C := C) base l .x14 19 r * winF' (Sl := Sl) (C := C) base l .x14 15 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x14 .y14, bcost φ 32) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x14 15) (winF' base l .x14 15) (winF base l .x14 19)
    (fun r _ => winF_inv base l .x14 15 r) (fun _ φ => bcost φ 32) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x14 .y14 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win13X base l hH t g _ (mainR g .x14 t)
  · exact win13Y base l hH t g _ (mainR g .y14 t)

/-- window 13 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg13 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x14 .y14
      then matAct f (winF (Sl := Sl) (C := C) base l .x14 19 r * winF' (Sl := Sl) (C := C) base l .x14 15 r) (y r)
      else y r)
      = win .x14 .y14 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 4).biUnion fun j => G19.incr l (15 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 15 3 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 15 3 (by norm_num)
  apply view_steps_win _ _ f y g t .x14 .y14 (by decide) _ (fun i => mem_ownerSet l .x14 .y14 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 19 = G19.setX l 15 ∪ ((Finset.range 4).biUnion fun j => G19.incr l (15 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y14 ≠ R34.x14)]
    rw [← matAct_mul]
    have e : G19.setY l 19 = G19.setY l 15 ∪ ((Finset.range 4).biUnion fun j => G19.incr l (15 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win14X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 15)) (frame (BBC (base t) l g) (G19.setX l 17))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setX l hH 15 (by norm_num)
  have h2 := G19.card_setX l hH 17 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 15 17 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win14Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 15)) (frame (BBC (base t) l g) (G19.setY l 17))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setY l hH 15 (by norm_num)
  have h2 := G19.card_setY l hH 17 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 15 17 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 14** (pair 15, stages 15..16) as an operator route (all gauges and ports). -/
theorem winSeg14 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x15 .y15
      then matAct f (winF (Sl := Sl) (C := C) base l .x15 17 r * winF' (Sl := Sl) (C := C) base l .x15 15 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x15 .y15, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x15 15) (winF' base l .x15 15) (winF base l .x15 17)
    (fun r _ => winF_inv base l .x15 15 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x15 .y15 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win14X base l hH t g _ (mainR g .x15 t)
  · exact win14Y base l hH t g _ (mainR g .y15 t)

/-- window 14 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg14 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x15 .y15
      then matAct f (winF (Sl := Sl) (C := C) base l .x15 17 r * winF' (Sl := Sl) (C := C) base l .x15 15 r) (y r)
      else y r)
      = win .x15 .y15 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G19.incr l (15 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 15 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 15 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x15 .y15 (by decide) _ (fun i => mem_ownerSet l .x15 .y15 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 17 = G19.setX l 15 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (15 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y15 ≠ R34.x15)]
    rw [← matAct_mul]
    have e : G19.setY l 17 = G19.setY l 15 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (15 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win15X (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setX l 17)) (frame (BBC (base t) l g) (G19.setX l 19))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setX l hH 17 (by norm_num)
  have h2 := G19.card_setX l hH 19 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G19.setX_mono l 17 19 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win15Y (t : T) (g : Orth (LC (Fin 18) H l)) :
    GReach (frame (BBC (base t) l g) (G19.setY l 17)) (frame (BBC (base t) l g) (G19.setY l 19))
      (fun φ => bcost φ 16) := by
  have h1 := G19.card_setY l hH 17 (by norm_num)
  have h2 := G19.card_setY l hH 19 (by norm_num)
  have h3 := G19.card_LC153 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G19.setY_mono l 17 19 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 15** (pair 16, stages 17..18) as an operator route (all gauges and ports). -/
theorem winSeg15 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x16 .y16
      then matAct f (winF (Sl := Sl) (C := C) base l .x16 19 r * winF' (Sl := Sl) (C := C) base l .x16 17 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x16 .y16, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x16 17) (winF' base l .x16 17) (winF base l .x16 19)
    (fun r _ => winF_inv base l .x16 17 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x16 .y16 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win15X base l hH t g _ (mainR g .x16 t)
  · exact win15Y base l hH t g _ (mainR g .y16 t)

/-- window 15 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg15 (f : ℕ) (y : Data (LC (Fin 18) H l) (PRole (Orth (LC (Fin 18) H l)) T Sl C) f)
    (g : Orth (LC (Fin 18) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x16 .y16
      then matAct f (winF (Sl := Sl) (C := C) base l .x16 19 r * winF' (Sl := Sl) (C := C) base l .x16 17 r) (y r)
      else y r)
      = win .x16 .y16 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G19.incr l (17 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G19.setX_add l 17 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G19.setY_add l 17 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x16 .y16 (by decide) _ (fun i => mem_ownerSet l .x16 .y16 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G19.setX l 19 = G19.setX l 17 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (17 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R34.y16 ≠ R34.x16)]
    rw [← matAct_mul]
    have e : G19.setY l 19 = G19.setY l 17 ∪ ((Finset.range 2).biUnion fun j => G19.incr l (17 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

end Win

end
end BQ19
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BQ19.winSeg0
#print axioms OAI.PowerSaving.BQ19.winSeg1
#print axioms OAI.PowerSaving.BQ19.winSeg2
#print axioms OAI.PowerSaving.BQ19.winSeg3
#print axioms OAI.PowerSaving.BQ19.winSeg4
#print axioms OAI.PowerSaving.BQ19.winSeg5
#print axioms OAI.PowerSaving.BQ19.winSeg6
#print axioms OAI.PowerSaving.BQ19.winSeg7
#print axioms OAI.PowerSaving.BQ19.winSeg8
#print axioms OAI.PowerSaving.BQ19.winSeg9
#print axioms OAI.PowerSaving.BQ19.winSeg10
#print axioms OAI.PowerSaving.BQ19.winSeg11
#print axioms OAI.PowerSaving.BQ19.winSeg12
#print axioms OAI.PowerSaving.BQ19.winSeg13
#print axioms OAI.PowerSaving.BQ19.winSeg14
#print axioms OAI.PowerSaving.BQ19.winSeg15
