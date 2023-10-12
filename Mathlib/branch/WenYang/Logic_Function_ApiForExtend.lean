/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.Tactic
--可以替换为 import Mathlib.Data.Set.Function
/-!
# APIs For `Function.Extend`

## Tags

extend
-/

-- 保存为 Mathlib/Logic/Function/ApiForExtend.lean

-- 标题 : feat: APIs of `Function.extend f g e'` when `f` is injective

-- We characterizes `range g`, `Injective g`, `Surjective g` and `Bijective g` in terms of `extend f g e'`.​

set_option autoImplicit true
open Function Set
variable {α : Sort u} (f : α → β) (g : α → γ) (e' : β → γ)

namespace Function

/-! ### Properties of `extend f g e'` when `f` is injective -/
section injective

variable (hf_i : Injective f)

-- 已经存在，这就是 Injective.extend_apply
-- theorem Injective.extend_mem_iff : g a = b ↔ (extend f g e') (f a) = b := by

-- theorem Injective.extend_eq : g = ((extend f g e') ∘ f) := by
--   exact (extend_comp hf_i g e').symm
--   done

theorem Injective.extend_image_eq : range g = (extend f g e') '' (range f) := by
  ext x
  simp [hf_i.extend_apply]

theorem Injective.extend_injOn : Injective g ↔ InjOn (extend f g e') (range f) := by
  rw [@injOn_iff_injective]
  unfold Injective
  simp [hf_i.extend_apply, hf_i.eq_iff]

theorem Injective.extend_surjOn : Surjective g ↔ SurjOn (extend f g e') (range f) univ := by
  rw [@surjOn_iff_surjective]
  unfold Surjective
  simp [hf_i.extend_apply, hf_i.eq_iff]

theorem Injective.extend_bijOn : Bijective g ↔ BijOn (extend f g e') (range f) univ := by
  unfold Bijective BijOn
  rw [← hf_i.extend_injOn, ← hf_i.extend_surjOn]
  simp only [iff_and_self, and_imp]
  exact fun _ _ ↦ mapsTo_univ (extend f g e') (range f)

end injective

end Function

section embedding

-- variable [TopologicalSpace α]  (hf_e : Embedding f)

-- theorem Embedding.extend_continuousOn : Continuous g ↔ ContinuousOn (extend f g e') (range f) := by

--   done

end embedding

-- #minimize_imports
