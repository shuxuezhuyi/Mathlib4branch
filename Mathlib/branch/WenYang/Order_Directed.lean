import Mathlib.Order.Directed
import Mathlib.Data.Set.Intervals.Basic
-- import Mathlib.Tactic
-- Yaël Dillies <yael.dillies@gmail.com>
variable {α β : Type*} [Preorder α] [PartialOrder β] {f : α → β}

/-- If `f` is monotone and antitone (increasing and decreasing) on `α` with a directed order, then `f` is constant.-/
lemma Monotone.directed_constant [IsDirected α (· ≤ ·)] (hf : Monotone f) (hf' : Antitone f) (a b : α) : f a = f b := by
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  exact le_antisymm ((hf hac).trans $ hf' hbc) ((hf hbc).trans $ hf' hac)

/-- If `f` is monotone and antitone (increasing and decreasing) on a directed set `s`, then `f` is constant on `s`.-/
lemma MonotoneOn.directedOn_constant {a b : α} {s : Set α}
    (hf : MonotoneOn f s) (hf' : AntitoneOn f s)
    (hs : DirectedOn (· ≤ ·) s)
    (ha : a ∈ s) (hb : b ∈ s) : f a = f b := by
  obtain ⟨c, hc, hac, hbc⟩ := hs _ ha _ hb
  exact le_antisymm ((hf ha hc hac).trans $ hf' hb hc hbc) ((hf hb hc hbc).trans $ hf' ha hc hac)
