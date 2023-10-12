import Mathlib.Data.Setoid.Partition

open IndexedPartition Function Set

namespace Set
/-- In a disjoint union we can identify the unique set an element belongs to.-/
theorem pairwiseDisjoint_unique {α ι : Type*} {y : α}
    (s : Set ι) (f : ι → Set α)
    (h_disjoint : PairwiseDisjoint s f)
    (hy : y ∈ (⋃ i ∈ s, f i)) : ∃! i, i ∈ s ∧ y ∈ f i := by
  refine exists_unique_of_exists_of_unique ?ex ?unique
  · rw [mem_iUnion] at hy
    choose i hi using hy
    use i
    rw [mem_iUnion] at hi
    exact exists_prop.mp hi
  · intro i j hi hj
    have : ¬Disjoint (f i) (f j) := not_disjoint_iff.mpr ⟨y, ⟨hi.2, hj.2⟩⟩
    exact PairwiseDisjoint.elim h_disjoint hi.1 hj.1 this
end Set