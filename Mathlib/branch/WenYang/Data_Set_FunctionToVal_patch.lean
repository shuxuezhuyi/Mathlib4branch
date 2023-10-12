import Mathlib.branch.WenYang.Data_Set_FunctionToVal
set_option autoImplicit true
open Set Function Set2Set
variable {s : Set α} {t : Set β} [Nonempty β]

-- 标题 : feat(Data/Set): Convert functions on subsets to functions between types

-- We define `Function.toval'` and provide some relevant APIs.

-- Co-authored-by: Yaël Dillies <yael.dillies@gmail.com>

noncomputable def Function.toval' (f : s → β) : α → β :=
  fun x =>
    haveI : Decidable (x ∈ s) := Classical.propDecidable _
    if hx : x ∈ s then f ⟨x, hx⟩
    else Classical.choice ‹_›

-- def id_univ (x : α) : (univ : Set α) := ⟨x, by trivial⟩

-- theorem id_univ_is_inv_val : (fun (x : (univ : Set α)) => x.val) ∘ id_univ = id := rfl

namespace Set2Set

/-! ### Equivalent definitions -/

theorem toval_eq_toval (f : s → t) : f.toval = (Subtype.val ∘ f).toval' := rfl

-- #check Equiv.Set.univ β

theorem toval_eq_toval' (f : s → β) : f.toval' = ((Equiv.Set.univ β).invFun ∘ f).toval := rfl

theorem toval_eq_extend' (f : s → β) :
    extend Subtype.val f (fun _ ↦ Classical.choice ‹_›) = f.toval' := by
  ext a
  unfold toval'
  split_ifs with ha
  · exact Subtype.val_injective.extend_apply _ _ (⟨a, ha⟩ : s)
  · refine extend_apply' _ _ _ ?_
    rintro ⟨a, rfl⟩
    exact ha a.2

theorem toval_eq_extend (f : s → t) : f.toval =
    extend Subtype.val (Subtype.val ∘ f) (fun _ ↦ Classical.choice ‹_›) := by
  rw [@toval_eq_extend', ← @toval_eq_toval]

/-! ### Properties of `Function.toval'` -/

theorem toval_eq' (f : s → β) : f = s.restrict f.toval' := by
  rw [@restrict_eq, @funext_iff]
  unfold toval'
  simp

-- 这个 mapsto 好像没有意义
-- theorem toval_mapsto' (f : s → β) : MapsTo f.toval' s univ := by
--   intro x
--   unfold toval'
--   simp

theorem toval_mem_iff' {f : s → β} : f a = b ↔ f.toval' a.val = b := by
  unfold toval'
  simp

theorem toval_image_eq' (f : s → β) : range f = f.toval' '' s := by
  rw [← @range_restrict, ← @toval_eq']

theorem toval_injOn' {f : s → β} : Injective f ↔ InjOn f.toval' s := by
  rw [@injOn_iff_injective, ← @toval_eq']
  -- rw [@toval_eq_toval', ← @toval_injOn]
  -- exact (Injective.of_comp_iff (Equiv.Set.univ β).symm.injective f).symm

theorem toval_surjOn' {f : s → β} : Surjective f ↔ SurjOn f.toval' s univ := by
  rw [@surjOn_iff_surjective, ← @toval_eq']

theorem toval_bijOn' {f : s → β} : Bijective f ↔ BijOn f.toval' s univ := by
  unfold Bijective BijOn
  rw [@toval_injOn', @toval_surjOn']
  simp only [iff_and_self, and_imp]
  exact fun _ _ ↦ mapsTo_univ (toval' f) s

theorem toval_continuous' [TopologicalSpace α] [TopologicalSpace β] {f : s → β} :
    Continuous f ↔ ContinuousOn f.toval' s := by
  rw [@continuousOn_iff_continuous_restrict, ← @toval_eq']

-- example {f : s → t} : Surjective f ↔ SurjOn f.toval s t := by
--   rw [toval_eq_extend]
--   rw [@val_surjOn]
--   unfold extend
--   simp [Subtype.coe_injective]
--   constructor
