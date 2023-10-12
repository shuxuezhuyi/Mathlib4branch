import Mathlib.Order.Directed
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.branch.WenYang.Order_Directed
-- import Mathlib.Tactic
variable {α β : Type*} [Preorder α] [PartialOrder β] {f : α → β}

open Set

theorem Icc.directedOn (a b : α) : DirectedOn (· ≤ ·) (Icc a b) := by
  intro x hx y hy
  use b
  simp only [ge_iff_le, gt_iff_lt, Set.mem_Icc, le_refl, and_true]
  exact ⟨le_trans hx.1 hx.2, hx.2, hy.2⟩

/-- If `f : [a, b] → β` is monotone and antitone (increasing and decreasing), then `f` is constant.-/
theorem MonotoneOn.Icc_constant {a b x y : α}
    (hf : MonotoneOn f (Icc a b)) (hf' : AntitoneOn f (Icc a b))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    f x = f y :=
    MonotoneOn.directedOn_constant hf hf' (Icc.directedOn a b) hx hy

/-- If `f : [a, b] → β` is strictly monotone and antitone (increasing and decreasing), then `f` is constant.-/
theorem StrictMonoOn.Icc_singleton {α : Type*} {a b : α} [PartialOrder α]
    {f : α → β} (hf : StrictMonoOn f (Icc a b)) (hf' : StrictAntiOn f (Icc a b))
    (hab : a ≤ b) : a = b := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  by_contra' h_ne
  replace hab : a < b := h_ne.lt_of_le hab
  exact (lt_trans (hf ha hb hab) (hf' ha hb hab)).false
