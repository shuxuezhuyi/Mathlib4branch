import Mathlib.Data.Setoid.Partition
import Mathlib.branch.WenYang.Data_Set_Pairwise_Lattice

open IndexedPartition Function Set

-- feat(Data/Setoid): another way to define piecewise functions

-- Use `IndexedPartition` to define `piecewise` functions. This is natural for piecewise functions that are split into many pieces.​

namespace IndexedPartition
-- 分段函数。注意：Set.piecewise, DFinsupp.piecewise, Finset.piecewise, Function.update, MeasureTheory.SimpleFunc.piecewise 也可用于构造分段函数
-- 你可以使用正则表达式 `def.*piecewise` 去搜索 mathlib4 里其它定义分段函数的方法。
/-- Combine functions with disjoint domains into a new function.
You can use the regular expression `def.*piecewise` to search for
other ways to define piecewise functions in mathlib4.-/
def piecewise {α β ι : Type*}
    (sα : ι → Set α) (hα : IndexedPartition sα)
    (f : ι → α → β) :
    α → β := fun x => f (hα.index x) x


-- 如果有一族单射，它们的定义域与值域都是两两不交的，那么它们可以粘合成一个单射。注意与 Set.pairwiseDisjoint_image_right_iff 的区别，后者是定义域相同、值域不同，粘合的时候把值域做成乘积空间了。
/-- A family of injective functions with pairwise disjoint
domains and pairwise disjoint ranges can be glued together
to form an injective function.-/
theorem piecewise_inj {α β ι : Type*}
    (sα : ι → Set α) (hα : IndexedPartition sα)
    (f : ι → α → β) (h_injOn : ∀ i, InjOn (f i) (sα i))
    (h_disjoint : PairwiseDisjoint (univ : Set ι) fun i => (f i) '' (sα i)):
    Injective (piecewise sα hα f) := by
  intro x y hfxy
  set F := fun i => (f i) '' (sα i)
  let i := index hα x
  have hix : piecewise sα hα f x = f i x := rfl
  let j := index hα y
  have hjy : piecewise sα hα f y = f j y := rfl
  have hz : piecewise sα hα f x ∈ (⋃ i ∈ univ, F i) := by
    simp only [mem_univ, iUnion_true, mem_iUnion, mem_image]
    unfold piecewise
    use i
    use x
    simp only [and_true]
    exact mem_index hα x
  choose k hk_exist hk_unique using pairwiseDisjoint_unique univ F h_disjoint hz
  set g := piecewise sα hα f
  have hik : i = k := hk_unique i ⟨trivial, by
    rw [hix]
    simp only [mem_image]
    use x
    simp only [and_true]
    exact mem_index hα x⟩
  have hjk : j = k := hk_unique j ⟨trivial, by
    rw [hfxy]
    rw [hjy]
    simp only [mem_image]
    use y
    simp only [and_true]
    exact mem_index hα y⟩
  have hij : i = j := hik.trans hjk.symm
  rw [hix, hjy, hij] at hfxy
  refine (h_injOn j) ?_ (mem_index hα y) hfxy
  rw [← hij]
  exact mem_index hα x

-- 注意：Set.BijOn.union
/-- A family of bijective functions with pairwise disjoint
domains and pairwise disjoint ranges can be glued together
to form a bijective function.-/
theorem piecewise_bij {α β ι : Type*}
    (sα : ι → Set α) (hα : IndexedPartition sα)
    (sβ : ι → Set β) (hβ : IndexedPartition sβ)
    (f : ι → α → β) (hf : ∀ i, BijOn (f i) (sα i) (sβ i)) :
    Bijective (piecewise sα hα f) := by
  set g := piecewise sα hα f
  have hg_bij : ∀ i, BijOn g (sα i) (sβ i) := by
    intro i
    refine BijOn.congr (hf i) ?_
    intro x hx
    unfold_let g
    unfold piecewise
    rw [hα.mem_iff_index_eq.mp hx]
  have hg_inj : InjOn g (⋃ i, sα i) := by
    refine injOn_of_injective ?_ (⋃ (i : ι), sα i)
    refine piecewise_inj sα hα f ?h_injOn ?h_disjoint
    · exact fun i ↦ BijOn.injOn (hf i)
    · unfold PairwiseDisjoint
      simp only [fun i => BijOn.image_eq (hf i)]
      intro i _ j _ hij
      exact hβ.disjoint hij
  have hg := bijOn_iUnion hg_bij hg_inj
  rw [hα.iUnion, hβ.iUnion] at hg
  exact bijective_iff_bijOn_univ.mpr hg

-- 分段严格单调

end IndexedPartition
