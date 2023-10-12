/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.Tactic
-- import Mathlib.Topology.ContinuousOn
/-!
# Convert functions between subsets to functions between types

把子类型之间的映射转换为类型之间的映射。

We define `Function.toval` and provide the relevant APIs.
我们定义 toval 并提供相关的接口。

## Main definitions

* `Function.toval` :
Given a function `f : s → t`, extend it to `f.toval : α → β` by
filling in the undefined parts with some constant function.
给定函数 `f : s → t`, 把它延拓为 `f.toval : α → β`, 用一个常值函数填充那些没有定义的地方。

## Main statements

* `toval_eq`:
`f` and `f.toval` are essentially equal on s.
f 与 f.toval 在 s 上本质上是相等的。

-/

-- 标题 : feat(Data/Set): Convert functions between subsets to functions between types

-- We define `Function.toval` and provide some relevant APIs.

set_option autoImplicit true

open Set Function

variable {s : Set α} {t : Set β} [Nonempty β]

/-- Given a function `f : s → t`, extend it to `f.toval : α → β` by
filling in the undefined parts with some constant function.
Notice that this constant function is not uniquely determined by `f`.-/
noncomputable def Function.toval (f : s → t) : α → β :=
  fun x =>
    haveI : Decidable (x ∈ s) := Classical.propDecidable _
    if hx : x ∈ s then (f ⟨x, hx⟩).val
    else Classical.choice ‹_›

namespace Set2Set

/-! ### Properties of `Function.toval` -/

theorem toval_eq (f : s → t) : (Subtype.val ∘ f) = (s.restrict f.toval) := by
  rw [@restrict_eq, @funext_iff]
  unfold toval
  simp

theorem toval_mapsto (f : s → t) : MapsTo f.toval s t := by
  intro x hx
  unfold toval
  aesop

theorem toval_mem_iff {f : s → t} : f a = b ↔ f.toval a.val = b.val := by
  constructor
  · unfold toval
    aesop
  · unfold toval
    simp only [Subtype.coe_prop, Subtype.coe_eta, dite_eq_ite, ite_true]
    exact fun x ↦ SetCoe.ext x

theorem toval_image_eq (f : s → t) : range (Subtype.val ∘ f) = f.toval '' s := by
  rw [@toval_eq]
  exact range_restrict (toval f) s

theorem toval_injOn {f : s → t} : Injective f ↔ InjOn f.toval s := by
  rw [@injOn_iff_injective, ← @toval_eq]
  exact (Injective.of_comp_iff Subtype.coe_injective f).symm

theorem val_surjOn {f : s → t} : Surjective f ↔ SurjOn (Subtype.val ∘ f) univ t := by
  constructor
  · intro hf_surj b hb
    choose a ha using hf_surj ⟨b, hb⟩
    rw [@mem_image]
    use a
    aesop
  · unfold SurjOn Surjective
    rw [@image_univ, @subset_def]
    intro left b
    choose a ha using left b b.property
    use a
    exact SetCoe.ext ha

theorem toval_surjOn {f : s → t} : Surjective f ↔ SurjOn f.toval s t := by
  rw [@val_surjOn, @toval_eq]
  constructor
  · intro left b hb
    choose a ha using left hb
    use a
    aesop
  · intro left b hb
    choose a ha using left hb
    aesop

theorem toval_bijOn {f : s → t} : Bijective f ↔ BijOn f.toval s t := by
  unfold Bijective BijOn
  rw [@toval_injOn, @toval_surjOn]
  simp only [iff_and_self, and_imp]
  exact fun _ _ ↦ toval_mapsto f

theorem toval_continuous [TopologicalSpace α] [TopologicalSpace β] {f : s → t} :
    Continuous f ↔ ContinuousOn f.toval s := by
  rw [@continuousOn_iff_continuous_restrict, ← @toval_eq, @continuous_induced_rng]

-- variable {ra : α → α → Prop} {rb : β → β → Prop}

-- 也许不需要这样一个结论
-- theorem toval_subrel {f : s → t} : (∀ (a b : s), Subrel ra s a b → Subrel rb t (f a) (f b)) ↔ (∀ a ∈ s, ∀ b ∈ s , ra a b → rb (f.toval a) (f.toval b)) := by
--   unfold toval
--   aesop

end Set2Set

example (ha : a ∉ s) (hb : b ∉ s) (f : s → t) : f.toval a = f.toval b := by
  unfold toval
  aesop

-- #minimize_imports
