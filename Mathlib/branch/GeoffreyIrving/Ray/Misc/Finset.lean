/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic.Rewrites

/-!
## `Finset ℕ` machinery for use in sums and products
-/

open Complex (abs)
open Filter (atTop)
open Stream' (cons)
open scoped Topology Stream

/-- Insert `0` into a `Finset ℕ`, adding `1` to existing elements -/
def push (N : Finset ℕ) :=
  insert 0 (Finset.image (fun n ↦ n + 1) N)

/-- Subtract `1` from everything in a `Finset ℕ`, discarding `0`.
    This is the left inverse of push. -/
def pop (N : Finset ℕ) :=
  Finset.image (fun n ↦ n - 1) (Finset.erase N 0)

/-- `push` almost cancels `pop` -/
theorem push_pop {N : Finset ℕ} : push (pop N) = insert 0 N := by
  rw [push, pop]; apply Finset.ext; simp
  intro n; by_cases n0 : n = 0; · rw [n0]; simp
  simp_rw [or_iff_right n0]
  constructor
  · intro h; rcases h with ⟨x, ⟨x0, xN⟩, xn⟩
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr x0)] at xn
    rwa [←xn]
  · intro h; exists n; use ⟨n0,h⟩
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr n0)

/-- `push` is monotone -/
theorem push_le_push {A B : Finset ℕ} : push A ≤ push B ↔ A ≤ B := by
  simp; rw [push]; rw [push]
  constructor
  · intro AB; rw [Finset.subset_iff] at AB ⊢; intro x xA
    have h : x + 1 ∈ insert 0 (Finset.image (fun n : ℕ ↦ n + 1) A) := by simpa
    specialize AB h; simp at AB; assumption
  · intro AB; apply Finset.insert_subset_insert; apply Finset.image_mono; assumption

/-- `push` and products interact nicely -/
theorem push_prod {a : ℂ} {f : ℕ → ℂ} {N : Finset ℕ} : a * N.prod f = (push N).prod (cons a f) := by
  rw [push]; simp; rfl

/-- The range of `push` is `Finset`s containing 0 -/
theorem push_range : Set.range push = {N : Finset ℕ | 0 ∈ N} := by
  rw [Set.range]; apply Set.ext; simp; intro N; constructor
  · intro h; rcases h with ⟨M, H⟩; rw [push] at H; rw [← H]; exact Finset.mem_insert_self 0 _
  · intro N0; exists pop N; rw [push_pop]; exact Finset.insert_eq_of_mem N0

theorem push_comap_atTop : Filter.comap push atTop = atTop := by
  apply Filter.comap_embedding_atTop
  exact @push_le_push
  intro N; exists pop N; rw [push_pop]; simp; exact Finset.subset_insert _ _

/-- `f ∘ push` converges `atTop` iff `f` does -/
theorem tendsto_comp_push {A : Type} {f : Finset ℕ → A} {l : Filter A} :
    Filter.Tendsto (f ∘ push) atTop l ↔ Filter.Tendsto f atTop l := by
  nth_rw 1 [← push_comap_atTop]; apply Filter.tendsto_comap'_iff
  rw [push_range]
  have h : {N : Finset ℕ | 0 ∈ N} = {N : Finset ℕ | {0} ≤ N} := by simp
  rw [h]; exact Filter.mem_atTop _

/-- Triangle inequality for finset sums of complex numbers -/
theorem finset_complex_abs_sum_le (N : Finset ℕ) (f : ℕ → ℂ) :
    abs (N.sum fun n ↦ f n) ≤ N.sum fun n ↦ abs (f n) := by
  induction' N using Finset.induction with n N Nn h; · simp
  · rw [Finset.sum_insert Nn]
    rw [Finset.sum_insert Nn]
    trans abs (f n) + abs (N.sum fun n ↦ f n); · exact Complex.abs.add_le _ _
    · apply add_le_add_left; assumption

theorem subset_union_sdiff (A B : Finset ℕ) : B ⊆ A ∪ B \ A := by
  rw [Finset.subset_iff]; intro x Bx
  rw [Finset.mem_union, Finset.mem_sdiff]
  by_cases Ax : x ∈ A
  · left; exact Ax
  · right; exact ⟨Bx, Ax⟩
