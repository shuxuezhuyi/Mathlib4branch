/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.Topology.Order.Basic
import Mathlib.branch.WenYang.Topology_Algebra_Order_IntermediateValue
import Mathlib.Topology.Homeomorph
import Mathlib.branch.WenYang.Data_Set_FunctionToVal
import Mathlib.branch.WenYang.Data_Setoid_Partition
import Mathlib.Tactic
-- 上面这行换成 import Mathlib.Data.Set.Intervals.Basic

/-!
# Extend the domain of f from an open interval to the closed interval

有时候一个映射 `f : (a, b) → β` 可以自然地延拓到 `[a, b]` 上。
Sometimes a mapping `f : (a, b) → β` can be naturally extended to `[a, b]`.

## Main statements

-/

-- 标题 : feat(Topology/Algebra/Order): extend function on `Ioo` to `Icc`

-- A strictly monotone function on an open interval can be extended to be strictly monotone on the closed interval.

open OrderDual TopologicalSpace Function Set
open Topology Filter
universe u
variable {α β : Type*} {f : α → β}

section monotone
variable [Preorder α] [Preorder β]

theorem MonotoneOn.restrict {s : Set α} (h : MonotoneOn f s): Monotone (s.restrict f) := by
  intro a b hab
  aesop

end monotone

variable [DecidableEq α]
/-
需要注意的事情：
严格单射有右逆则是序同构，orderIsoOfRightInverse
严格单调递增自然诱导序同构，StrictMonoOn.orderIso
单调函数的连续性，Mathlib/Topology/Algebra/Order/MonotoneContinuity.lean
单调满射且值域densely ordered，必定连续，Monotone.continuous_of_surjective
分段函数也有 Set.piecewise，但在这里似乎不好用
-/

section update
variable {s : Set α} {a : α} {b : β}
-- 如果 `a` 是 `s` 的严格上界，并且 `b` 是 `f(s)` 的严格上界，那么在 `s` 上严格单调递增的 `f` 可以延拓为在 `s ∪ {a}` 上严格单调递增。
/-- If `a` is a strict upper bound of `s`,
`b` is a strict upper bound of `f(s)`,
and `f` is strictly monotone (increasing) on `s`,
then `f` can be extended to be strictly monotone (increasing) on `s ∪ {a}`.-/
theorem StrictMonoOn.update_strict_upper_bound  [PartialOrder α] [Preorder β]
    (hf_mono : StrictMonoOn f s) (hf_mapsto : f '' s ⊆ Iio b)
    (ha : ∀ x ∈ s, x < a) :
    StrictMonoOn (update f a b) (s ∪ {a}) := by
  unfold update
  simp only [eq_rec_constant, dite_eq_ite, union_singleton]
  intro x hx y hy hxy
  simp only
  have hxa : x ≠ a := by
    by_contra' hxa
    rw [hxa] at hxy
    cases hy with
    | inl h => rw [h] at hxy; exact hxy.false
    | inr h => exact (hxy.trans (ha y h)).false
  by_cases hya : y = a
  aesop
  aesop

-- 如果 `a` 是 `s` 的严格下界，并且 `b` 是 `f(s)` 的严格下界，那么在 `s` 上严格单调递减的 `f` 可以延拓为在 `s ∪ {a}` 上严格单调递减。
/-- If `a` is a strict lower bound of `s`,
`b` is a strict lower bound of `f(s)`,
and `f` is strictly antitone (decreasing) on `s`,
then `f` can be extended to be strictly antitone (decreasing) on `s ∪ {a}`.-/
theorem StrictMonoOn.update_strict_lower_bound [PartialOrder α] [Preorder β]
    (hf_mono : StrictMonoOn f s) (hf_mapsto : f '' s ⊆ Ioi b)
    (ha : ∀ x ∈ s, a < x) :
    StrictMonoOn (update f a b) (s ∪ {a}) := by
  let g : OrderDual α → OrderDual β := f
  have hg_mono : StrictMonoOn g s := strict_mono_on_dual_iff.mp hf_mono
  have := hg_mono.update_strict_upper_bound hf_mapsto ha
  exact strict_mono_on_dual_iff.mp this

-- 为 Function.update 增加一个引理
-- 只是修改 `f` 在 `a` 处的函数值，不会影响 `f` 在别的地方的函数值。
/-- Modifying the value of `f` at one point does not affect its value elsewhere.​-/
theorem Function.update.EqOn (f : α → β) (ha : a ∉ s) : EqOn (update f a b) f s := by
  intro x hx
  unfold update
  simp only [eq_rec_constant, dite_eq_ite]
  have : x ≠ a := ne_of_mem_of_not_mem hx ha
  aesop

theorem Function.update.image (f : α → β) (ha : a ∉ s) : (update f a b) '' (s ∪ {a}) = f '' s ∪ {b} := by
  calc
    _ = (update f a b) '' s ∪ (update f a b) '' {a} := image_union (update f a b) s {a}
    _ = (update f a b) '' s ∪ {b} := by simp
    _ = f '' s ∪ {b} := by simp only [(update.EqOn f ha).image_eq]

end update

open Set2Set

section StrictMonoOn
variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β] [Nonempty β]
    {a b : α} {c d : β}

-- 标题 : feat(Topology/Algebra/Order): continuously extend function strictly monotone on `Ioo` to `Icc`

-- A strictly monotone function on an open interval can be continuously extended to the closed interval.

/-- Extend strictly monotone (increasing) functions between open intervals to homeomorphisms
between the closed intervals.-/
theorem StrictMonoOn.Ioo_continuous_extend_Icc (hf_increasing : StrictMonoOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) = Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ (g : (Icc a b) ≃ₜ (Icc c d)), EqOn f g.toFun.toval (Ioo a b) := by
  let g := update (update f a c) b d
  --  First, we verify that `g` is strictly monotone.
  have ha : a ∉ Ioo a b := by simp
  have ha' : Ico a b = (Ioo a b) ∪ {a} := (Ioo_union_left hab).symm
  have hf_mono' : StrictMonoOn (update f a c) (Ico a b) := by
    rw [ha']
    refine hf_increasing.update_strict_lower_bound ?mapsto ?ha
    · rw [hf_mapsto]
      exact Ioo_subset_Ioi_self
    · aesop
  have hf_mapsto' : (update f a c) '' (Ico a b) = Ico c d := by
    rw [ha', image_union]
    simp only [(update.EqOn f ha).image_eq]
    aesop
  have : (update f a c) '' (Ico a b) ⊆ Iio d := by
    rw [hf_mapsto']
    exact Ico_subset_Iio_self
  have hb : ∀ x ∈ Ico a b, x < b := by simp
  have hf_mono'' := hf_mono'.update_strict_upper_bound this hb
  replace : Ico a b ∪ {b} = Icc a b := Ico_union_right hab.le
  rw [this] at hf_mono''
  have hg_mono : StrictMonoOn g (Icc a b) := hf_mono''
  -- Second, we verify that the image of `g` is `[c, d]`.
  have hg_mapsto : g '' Icc a b = Icc c d := by
    unfold_let g
    have hb : b ∉ Ico a b := by simp
    rw [← Ico_union_right hab.le, update.image (update f a c) hb, ← Ioo_union_left hab,
        update.image f ha, hf_mapsto, Ioo_union_left hcd, Ico_union_right hcd.le]
  -- Third, we find that `g` is an order isomorphism.
  let iso := hg_mono.orderIso g _
  have hg_image : OrderTopology (g '' (Icc a b)) := by
    rw [hg_mapsto]
    exact orderTopology_of_ordConnected
  let F := iso.toHomeomorph
  have h_eq_fg : EqOn f g (Ioo a b) := by
    intro x hx
    unfold_let g
    unfold update
    have hxa : x ≠ a := by
      by_contra'
      rw [this] at hx
      revert hx
      simp
    have hxb : x ≠ b := by
      by_contra'
      rw [this] at hx
      revert hx
      simp
    simp [hxa, hxb]
  have h_eq_gF : EqOn g (toval iso.toFun) (Icc a b) := by
    rw [← @restrict_eq_restrict_iff, ← toval_eq, @restrict_eq]
    exact rfl
  have hF : EqOn f (toval F.toFun) (Ioo a b) := by
    intro x hx
    rw [h_eq_fg hx, h_eq_gF (mem_Icc_of_Ioo hx)]
    exact rfl
  have : ∃ (G : (Icc a b) ≃ₜ (g '' Icc a b)), EqOn f G.toFun.toval (Ioo a b) := by use F
  rw [hg_mapsto] at this
  exact this

/-- Extend strictly antitone (decreasing) functions between open intervals to homeomorphisms
between the closed intervals.-/
theorem StrictAntiOn.Ioo_continuous_extend_Icc (hf_decreasing : StrictAntiOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) = Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ (g : (Icc a b) ≃ₜ (Icc c d)), EqOn f g.toFun.toval (Ioo a b) := by
  let F : α → OrderDual β := f
  have hF_increasing : StrictMonoOn F (Ioo a b) := hf_decreasing
  have hF_mapsto : F '' (Ioo a b) = Ioo (toDual d) (toDual c) := by aesop
  obtain h := hF_increasing.Ioo_continuous_extend_Icc hF_mapsto hab hcd
  have : Icc (toDual d) (toDual c) = Icc c d := by aesop
  rw [this] at h
  exact h

end StrictMonoOn

section ContinuousOn
open TopologicalSpace
variable [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β][OrderClosedTopology β] [Nonempty β]
    {a b : α} {c d : β}

theorem Homeomorph.Ioo_extend_Icc (f : (Ioo a b) ≃ₜ (Ioo c d)) (hab : a < b) (hcd : c < d) :
    ∃ (g : (Icc a b) ≃ₜ (Icc c d)), EqOn (toval f) (toval g) (Ioo a b) := by
  have hf_c : ContinuousOn (toval f) (Ioo a b) := by
    rw [← toval_continuous]
    exact f.continuous
  have hf_inj : InjOn (toval f) (Ioo a b) := by
    rw [← toval_injOn]
    exact f.injective
  have hf_mapsto : (toval f) '' (Ioo a b) = Ioo c d := by
    rw [← toval_image_eq, @EquivLike.range_comp, @Subtype.range_val]
  have hf_mono := hf_c.StrictMonoOn_of_InjOn_Ioo hab hf_inj
  cases hf_mono with
  | inl hf_mono =>
    exact StrictMonoOn.Ioo_continuous_extend_Icc hf_mono hf_mapsto hab hcd
  | inr hf_mono =>
    exact StrictAntiOn.Ioo_continuous_extend_Icc hf_mono hf_mapsto hab hcd

end ContinuousOn
