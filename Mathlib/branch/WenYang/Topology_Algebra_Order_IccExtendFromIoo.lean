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

* `StrictMonoOn.Ioo_extend_Icc` and `StrictAntiOn.Ioo_extend_Icc`:
A strictly monotone function on an open interval can be extended to be
strictly monotone on the closed interval.
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

-- section StrictMonoOn
-- variable [PartialOrder α] [PartialOrder β]  {a b : α} {c d : β}
-- -- 在开区间上严格单调递增的函数可以延拓为闭区间上严格单调递增的函数
-- /-- A strictly monotone (increasing) function on an open interval can be extended
-- to be strictly monotone (increasing) on the closed interval.-/
-- theorem StrictMonoOn.Ioo_extend_Icc (hf_mono : StrictMonoOn f (Ioo a b))
--     (hf_mapsto : f '' (Ioo a b) ⊆ Ioo c d) (hab : a < b) (hcd : c < d) :
--     ∃ g, StrictMonoOn g (Icc a b) ∧
--     EqOn f g {a, b}ᶜ ∧
--     g '' (Icc a b) = f '' (Ioo a b) ∪ {c, d} ∧
--     g = update (update f a c) b d := by
--   let g : α → β := update (update f a c) b d
--   use g
--   have ha : a ∉ Ioo a b := by simp
--   have hg_mono : StrictMonoOn g (Icc a b) := by
--     have ha' : Ico a b = (Ioo a b) ∪ {a} := (Ioo_union_left hab).symm
--     have hf_mono' : StrictMonoOn (update f a c) (Ico a b) := by
--       rw [ha']
--       refine hf_mono.update_strict_lower_bound ?mapsto ?ha
--       · exact hf_mapsto.trans Ioo_subset_Ioi_self
--       · aesop
--     have hf_mapsto' : (update f a c) '' (Ico a b) ⊆ Ico c d := by
--       rw [ha', image_union]
--       simp only [(update.EqOn f ha).image_eq]
--       rw [← Ioo_union_left hcd]
--       simp [insert_subset_insert hf_mapsto]
--     have : (update f a c) '' (Ico a b) ⊆ Iio d := hf_mapsto'.trans Ico_subset_Iio_self
--     have hb : ∀ x ∈ Ico a b, x < b := by simp
--     have hf_mono'' := hf_mono'.update_strict_upper_bound this hb
--     replace : Ico a b ∪ {b} = Icc a b := Ico_union_right hab.le
--     rw [this] at hf_mono''
--     exact hf_mono''
--   have hg_eq : EqOn f g {a, b}ᶜ := by
--     intro x hx
--     unfold_let g
--     unfold update
--     aesop
--   have hg_image : g '' Icc a b = f '' Ioo a b ∪ {c, d} := by
--     unfold_let g
--     have hb : b ∉ Ico a b := by simp
--     rw [← Ico_union_right hab.le, update.image (update f a c) hb,
--         ← Ioo_union_left hab, update.image f ha]
--     have := insert_comm d c (f '' Ioo a b)
--     simp [this]
--   trivial



-- -- 在开区间上严格单调递减的函数可以延拓为闭区间上严格单调递减的函数
-- /-- A strictly antitone (decreasing) function on an open interval can be extended
-- to be strictly antitone (decreasing) on the closed interval.-/
-- theorem StrictAntiOn.Ioo_extend_Icc (hf_mono : StrictAntiOn f (Ioo a b))
--     (hf_mapsto : f '' (Ioo a b) ⊆ Ioo c d) (hab : a < b) (hcd : c < d) :
--     ∃ g, StrictAntiOn g (Icc a b) ∧
--     EqOn f g {a, b}ᶜ ∧
--     g '' (Icc a b) = f '' (Ioo a b) ∪ {c, d} ∧
--     g = update (update f a d) b c := by
--   let g : α → OrderDual β := f
--   have hg_mono : StrictMonoOn g (Ioo a b) := hf_mono
--   have hg_mapsto : g '' (Ioo a b) ⊆ Ioo (toDual d) (toDual c) := by aesop
--   choose G hG using hg_mono.Ioo_extend_Icc hg_mapsto hab hcd
--   let F : α → β := G
--   use F
--   constructor
--   · aesop
--   · constructor
--     · aesop
--     · constructor
--       · rw [hG.2.2.1]
--         have := insert_comm (toDual d) (toDual c) ((fun a ↦ f a) '' Ioo a b)
--         aesop
--       · aesop



-- end StrictMonoOn
-- LocalHomeomorph 的定义太奇怪了

open Set2Set

section StrictMonoOn
variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β] [Nonempty β]
    {a b : α} {c d : β}

-- 标题 : feat(Topology/Algebra/Order): continuously extend function strictly monotone on `Ioo` to `Icc`

-- A strictly monotone function on an open interval can be continuously extended to the closed interval.

-- TODO: 条件 `StrictMonoOn f` 应当减弱为 `MonotoneOn f`, 但需要别的证明思路，因为下面用到了 `StrictMonoOn.orderIso`
-- 在开区间上严格单调递增的函数可以连续延拓到闭区间上
/- TODO: The condition `StrictMonoOn f` should be weakened to `MonotoneOn f`,
but we need a different proof since `StrictMonoOn.orderIso` is used below.-/
-- 删掉上述 TODO

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

  -- let g' := f.invFun
  -- have hg_c' : ContinuousOn g'.toval (Ioo c d) := by
  --   rw [← toval_continuous]
  --   exact f.continuous_invFun
  -- have hg_inj' : InjOn g'.toval (Ioo c d) := by
  --   rw [← toval_injOn]
  --   exact f.symm.injective
  -- have hg_bij' : BijOn g'.toval (Ioo c d) (Ioo a b) := by
  --   rw [← toval_bijOn]
  --   exact f.symm.bijective
  -- have hg_mapsto' : g'.toval '' (Ioo c d) = (Ioo a b) := hg_bij'.image_eq
  -- choose G' hG' using hg_c'.injOn_Ioo_extend_Icc hg_mapsto' hg_inj' hab hcd

end ContinuousOn
-- /-- Another version of `LocalEquiv`, but focus on subsets.-/
-- structure SubsetEquiv {α β : Type*} (source : Set α) (target : Set β) where
--   /-- The global function which has a local inverse. Its value outside of the `source` subset is
--   irrelevant. -/
--   toFun : α → β
--   /-- The local inverse to `toFun`. Its value outside of the `target` subset is irrelevant. -/
--   invFun : β → α
--   /-- The proposition that elements of `source` are mapped to elements of `target`. -/
--   map_source' : MapsTo toFun source target
--   /-- The proposition that elements of `target` are mapped to elements of `source`. -/
--   map_target' : MapsTo invFun target source
--   /-- The proposition that `invFun` is a local left-inverse of `toFun` on `source`. -/
--   left_inv' : ∀ ⦃x⦄, x ∈ source → invFun (toFun x) = x
--   /-- The proposition that `invFun` is a local right-inverse of `toFun` on `target`. -/
--   right_inv' : ∀ ⦃x⦄, x ∈ target → toFun (invFun x) = x

-- /-- The domain of the local equivalence. -/
-- def SubsetEquiv.source {α β : Type*} {s : Set α} {t : Set β} (_ : SubsetEquiv s t) : Set α := s

-- /-- The codomain of the local equivalence. -/
-- def SubsetEquiv.target {α β : Type*} {s : Set α} {t : Set β} (_ : SubsetEquiv s t) : Set β := t

-- -- instance DefEq_LocalEquiv {α β : Type*} {s : Set α} {t : Set β} : CoeOut (SubsetEquiv s t) (LocalEquiv α β) := ⟨
-- --   fun (f : SubsetEquiv s t) => ⟨
-- --     f.toFun,
-- --     f.invFun,
-- --     s,
-- --     t,
-- --     f.map_source',
-- --     f.map_target',
-- --     f.left_inv',
-- --     f.right_inv'
-- --     ⟩
-- --   ⟩

-- def SubsetEquiv.toLocalEquiv {α β : Type*} {s : Set α} {t : Set β} (f : SubsetEquiv s t) : (LocalEquiv α β) := ⟨f.toFun, f.invFun, s, t, f.map_source', f.map_target', f.left_inv', f.right_inv'⟩

-- instance {α β : Type*} {s : Set α} {t : Set β} : CoeFun (SubsetEquiv s t) fun _ => α → β :=
--   ⟨SubsetEquiv.toFun⟩

-- -- theorem SubsetEquiv.injOn {α β : Type*} {s : Set α} {t : Set β} (f : SubsetEquiv s t) : InjOn f s := by
-- --   have : InjOn f f.source := LocalEquiv.injOn f

-- -- def SubsetEquiv' {α β : Type*} (source : Set α) (target : Set β) : SubsetEquiv α β where


-- structure SubsetHomeomorph' {α β : Type*} [TopologicalSpace α]
--   [TopologicalSpace β] (source : Set α) (target : Set β) extends SubsetEquiv source target where
--   continuous_toFun : ContinuousOn toFun source
--   continuous_invFun : ContinuousOn invFun target

-- structure SubsetHomeomorph {α β : Type*} [TopologicalSpace α]
--   [TopologicalSpace β] (source : Set α) (target : Set β) extends LocalEquiv α β where
--   continuous_toFun : ContinuousOn toFun source
--   continuous_invFun : ContinuousOn invFun target

-- noncomputable def SubsetHomeomorph.Ioo_extend_Icc {α : Type*} [ConditionallyCompleteLinearOrder α]
--     [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
--     {β : Type*} [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] [DecidableEq α] {a b : α} {c d : β} (f : SubsetHomeomorph (Ioo a b) (Ioo c d)) (hab : a < b) : ∃ (g : α → β), ContinuousOn g (Icc a b) := by
--   have hf_inj : InjOn f.toFun f.source := LocalEquiv.injOn f.toLocalEquiv
--   have : f.source = Ioo a b := by
--   have hf := f.continuous_toFun.StrictMonoOn_of_InjOn_Ioo hab
--   by_cases hg : StrictMonoOn  (Icc a b)
