/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang, Johan Commelin
-/
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.branch.WenYang.Order_Directed
import Mathlib.branch.WenYang.Data_Set_Intervals_Image
-- Co-authored-by: Johan Commelin <johan@commelin.net>
/-!
# 连续单射必定严格单调
-/
open Filter OrderDual TopologicalSpace Function Set
open Topology Filter
universe u
variable {α : Type u} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderClosedTopology δ]
-- 为了使用 intermediate_value_Ioo 做准备
/-- Suppose `f : [a, b] → δ` is
continuous and injective. Then `f` is strictly monotone (increasing)
if `f(a) < f(b)`.-/
theorem ContinuousOn.StrictMonoOn_of_InjOn_Icc {a b : α} {f : α → δ} (hab : a ≤ b) (hfab : f a ≤ f b)
    (hf_c : ContinuousOn f (Icc a b)) (hf_i : InjOn f (Icc a b)) :
    StrictMonoOn f (Icc a b) := by
-- I learned this proof from
-- <https://www.math.cuhk.edu.hk/course_builder/2021/math1050b/1050b-l14h-3.pdf>
  intro s hs t ht hst
  by_contra' hfts
  replace hfts : f t < f s := lt_of_le_of_ne hfts <| hf_i.ne ht hs hst.ne'
  by_cases hsa : f s ≤ f a
  · have hat : Icc t b ⊆ Icc a b := Icc_subset_Icc_left ht.1
    have : f a ∈ Ioc (f t) (f b) := ⟨(hfts.trans_le hsa), hfab⟩
    obtain ⟨u, hu⟩ : f a ∈ f '' Ioc t b :=
      intermediate_value_Ioc ht.2 (hf_c.mono hat) this
    apply (lt_of_lt_of_le' hu.1.1 ht.1).ne'
    exact hf_i (hat (Ioc_subset_Icc_self hu.1)) (left_mem_Icc.mpr hab) hu.2
  · by_cases hat : f a < f t
    · have hsb : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
      obtain ⟨u, hu⟩ : f t ∈ f '' Ioo a s :=
        intermediate_value_Ioo hs.1 (hf_c.mono hsb) ⟨hat, hfts⟩
      apply (hu.1.2.trans hst).ne
      exact hf_i (hsb (Ioo_subset_Icc_self hu.1)) ht hu.2
    · push_neg at hsa hat
      have : a ≠ t := (lt_of_lt_of_le' hst hs.1).ne
      have : f a ≠ f t := hf_i.ne (left_mem_Icc.mpr hab) ht this
      replace hat : f t < f a := this.symm.lt_of_le hat
      have hstab : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
      obtain ⟨u, hu⟩ : f a ∈ f '' Ioo s t :=
        intermediate_value_Ioo' hst.le (hf_c.mono hstab) ⟨hat, hsa⟩
      apply (lt_of_lt_of_le' hu.1.1 hs.1).ne'
      exact hf_i (hstab (Ioo_subset_Icc_self hu.1)) (left_mem_Icc.mpr hab) hu.2

/-- Suppose `f : [a, b] → δ` is
continuous and injective. Then `f` is strictly antitone (decreasing)
if `f(a) > f(b)`.-/
theorem ContinuousOn.StrictAntiOn_of_InjOn_Icc {a b : α} {f : α → δ} (hab : a ≤ b) (hfab : f b ≤ f a)
    (hf_c : ContinuousOn f (Icc a b)) (hf_i : InjOn f (Icc a b)) :
    StrictAntiOn f (Icc a b) := by
    let g (x : α) : OrderDual δ := f x
    have hgab : g a ≤ g b := hfab
    exact ContinuousOn.StrictMonoOn_of_InjOn_Icc hab hgab hf_c hf_i

/-- Suppose `f : [a, b] → δ` is continuous and injective. Then `f` is strictly monotone.-/
theorem ContinuousOn.StrictMonoOn_of_InjOn_Icc' {a b : α} {f : α → δ} (hab : a ≤ b)
    (hf_c : ContinuousOn f (Icc a b)) (hf_i : InjOn f (Icc a b)) :
    StrictMonoOn f (Icc a b) ∨ StrictAntiOn f (Icc a b) :=
  (le_total (f a) (f b)).imp
    (ContinuousOn.StrictMonoOn_of_InjOn_Icc hab · hf_c hf_i)
    (ContinuousOn.StrictAntiOn_of_InjOn_Icc hab · hf_c hf_i)

/- 这个定理仅用于证明 ContinuousOn.StrictMonoOn_of_InjOn_Ioo.
它断言，连续单射 f : (a, b) → δ 在每个闭区间 [c, d] ⊆ (a, b) 上必定严格单调。-/
/-- This lemma is only used to
prove and will be immediately superseded by
`ContinuousOn.StrictMonoOn_of_InjOn_Ioo` below.
It asserts that every continuous injective `f: (a, b) → δ` is strictly monotone on
every closed interval `[c, d] ⊆ (a, b)`.-/
private lemma ContinuousOn.StrictMonoOn_of_InjOn_Ioo_subinterval {a b : α} {f : α → δ}
    (hf_c : ContinuousOn f (Ioo a b)) (hf_i : InjOn f (Ioo a b))
    {c d : α} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) (hcd : c ≤ d) :
    StrictMonoOn f (Icc c d) ∨ StrictAntiOn f (Icc c d) :=
  ContinuousOn.StrictMonoOn_of_InjOn_Icc' hcd (hf_c.mono h) (hf_i.mono h) where
  h : Icc c d ⊆ Ioo a b := (Ioo a b).Icc_subset hc hd

/- 这个定理仅用于证明 ContinuousOn.StrictMonoOn_of_InjOn_Ioo.
它断言，连续单射 f : (a, b) → δ 如果在某个闭区间 [c, d] ⊆ (a, b) 上严格单调递增，就会在整个 (a, b) 上严格单调递增。-/
/-- This lemma is only used to
prove and will be immediately superseded by
`ContinuousOn.StrictMonoOn_of_InjOn_Ioo` below.
It asserts that a continuous injective `f: (a, b) → δ` is strictly monotone (increasing) if
it is strictly monotone (increasing) on some closed interval `[c, d] ⊆ (a, b)`.-/
private lemma ContinuousOn.StrictMonoOn_of_InjOn_Ioo_rigidity {a b : α} {f : α → δ}
    {c d : α} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) (hcd : c < d)
    (hf_c : ContinuousOn f (Ioo a b)) (hf_i : InjOn f (Ioo a b))
    (hf_mono : StrictMonoOn f (Icc c d)) : StrictMonoOn f (Ioo a b) := by
  intro x hx y hy hxy
  let s := min c x
  let t := max d y
  have hsc : s ≤ c := min_le_left c x
  have hdt : d ≤ t := le_max_left d y
  have hs : s ∈ Ioo a b := ⟨lt_min hc.1 hx.1, min_lt_of_left_lt hc.2⟩
  have ht : t ∈ Ioo a b := ⟨lt_max_of_lt_right hy.1, max_lt hd.2 hy.2⟩
  have hst : s ≤ t := hsc.trans $ hdt.trans' hcd.le
  have hf_mono_st : StrictMonoOn f (Icc s t) ∨ StrictAntiOn f (Icc s t) :=
    ContinuousOn.StrictMonoOn_of_InjOn_Ioo_subinterval hf_c hf_i hs ht hst
  have (h : StrictAntiOn f (Icc s t)) : False := by
    have : Icc c d ⊆ Icc s t := Icc_subset_Icc hsc hdt
    replace : StrictAntiOn f (Icc c d) := StrictAntiOn.mono h this
    replace : c = d := StrictMonoOn.Icc_singleton hf_mono this hcd.le
    apply hcd.ne
    exact this
  replace hf_mono_st : StrictMonoOn f (Icc s t) := hf_mono_st.resolve_right this
  have hsx : s ≤ x := min_le_right c x
  have hyt : y ≤ t := le_max_right d y
  replace : Icc x y ⊆ Icc s t := Icc_subset_Icc hsx hyt
  replace : StrictMonoOn f (Icc x y) := StrictMonoOn.mono hf_mono_st this
  exact this (left_mem_Icc.mpr (le_of_lt hxy))
    (right_mem_Icc.mpr (le_of_lt hxy)) hxy
/- 连续单射 f : (a, b) → δ 必定严格单调。-/
/-- Every continuous injective `f : (a, b) → δ` is strictly monotone.-/
theorem ContinuousOn.StrictMonoOn_of_InjOn_Ioo {a b : α} {f : α → δ} (hab : a < b)
    (hf_c : ContinuousOn f (Ioo a b)) (hf_i : InjOn f (Ioo a b)) :
    StrictMonoOn f (Ioo a b) ∨ StrictAntiOn f (Ioo a b) := by
  choose c hc using nonempty_Ioo.mpr hab
  choose d hd using nonempty_Ioo.mpr hc.2
  have hcd : c < d := hd.1
  replace hd : d ∈ Ioo a b := ⟨lt_trans hc.1 hcd, hd.2⟩
  have hf_mono_cd : StrictMonoOn f (Icc c d) ∨ StrictAntiOn f (Icc c d) :=
    ContinuousOn.StrictMonoOn_of_InjOn_Ioo_subinterval hf_c hf_i hc hd hcd.le
  have (h : StrictAntiOn f (Icc c d)) : StrictAntiOn f (Ioo a b) := by
    let g (x : α) : OrderDual δ := f x
    have : StrictMonoOn g (Ioo a b) := ContinuousOn.StrictMonoOn_of_InjOn_Ioo_rigidity hc hd hcd hf_c hf_i h
    exact this
  exact hf_mono_cd.imp (ContinuousOn.StrictMonoOn_of_InjOn_Ioo_rigidity hc hd hcd hf_c hf_i) this
