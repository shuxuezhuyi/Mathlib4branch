/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.branch.GeoffreyIrving.Ray.Analytic.Analytic
import Mathlib.branch.GeoffreyIrving.Ray.Misc.Bounds
import Mathlib.branch.GeoffreyIrving.Ray.Misc.Finset
import Mathlib.branch.GeoffreyIrving.Ray.Analytic.Holomorphic
import Mathlib.branch.GeoffreyIrving.Ray.Analytic.Series
import Mathlib.branch.GeoffreyIrving.Ray.Tactic.Bound

/-!
## Infinite products of analytic functions

We define convergence of infinite products, and show that uniform limits of products of
analytic functions are analytic.
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Complex (abs exp log)
open Filter (atTop)
open Metric (ball closedBall sphere)
open scoped Classical Real NNReal ENNReal Topology
noncomputable section

/-- The infinite product of `f n` converges absolutely to `g` (analogous to `HasSum`) -/
def HasProd (f : ℕ → ℂ) (g : ℂ) :=
  Filter.Tendsto (fun N : Finset ℕ ↦ N.prod fun n ↦ f n) atTop (𝓝 g)

/-- For all z, `Πₙ f n z` converges absolutely to `g z` (analogous to `HasSumOn`) -/
def HasProdOn (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : Set ℂ) :=
  ∀ z, z ∈ s → HasProd (fun n ↦ f n z) (g z)

/-- The product of `f` converges absolutely to something (analogous to `Summable`) -/
def ProdExists (f : ℕ → ℂ) : Prop :=
  ∃ g, HasProd f g

/-- The limit of an infinite product if it exists, or `0` -/
noncomputable def tprod (f : ℕ → ℂ) :=
  if h : ProdExists f then Classical.choose h else 0

/-- The limit of an infinite product if it exists, or `0` -/
noncomputable def tprodOn (f : ℕ → ℂ → ℂ) := fun z ↦ tprod fun n ↦ f n z

/-- The limit of a parameterized infinite product if it exists, or `0` -/
def ProdExistsOn (f : ℕ → ℂ → ℂ) (s : Set ℂ) :=
  ∀ z, z ∈ s → ProdExists fun n ↦ f n z

/-- Products are unique -/
theorem HasProd.unique {f : ℕ → ℂ} {a b : ℂ} : HasProd f a → HasProd f b → a = b :=
  tendsto_nhds_unique

/-- If a product has a particular limit, it has some limit -/
theorem HasProd.prodExists {f : ℕ → ℂ} {g : ℂ} (h : HasProd f g) : ProdExists f :=
  ⟨g, h⟩

/-- `tprod` is the product limit if it exists -/
theorem HasProd.tprod_eq {f : ℕ → ℂ} {g : ℂ} : HasProd f g → tprod f = g := by
  intro h; rw [tprod]; simp only [h.prodExists, dif_pos]
  exact (Classical.choose_spec h.prodExists).unique h

/-- `tprodOn` is the product on `s` if it exists on `s` -/
theorem HasProdOn.tprodOn_eq {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {s : Set ℂ} :
    HasProdOn f g s → ∀ z, z ∈ s → tprodOn f z = g z := fun h z zs ↦ (h z zs).tprod_eq

/-- The product of ones is one -/
theorem prod_ones : HasProd (fun _ ↦ (1 : ℂ)) 1 := by
  simp only [HasProd, Finset.prod_const_one, tendsto_const_nhds_iff]

/-- The product of ones is one (`tprod` version) -/
theorem prod_ones' : (tprod fun _ ↦ (1 : ℂ)) = 1 :=
  HasProd.tprod_eq prod_ones

/-- Analytic products that converge exponentially converge to analytic functions.
    For now, we require the constant to be `≤ 1/2` so that we can take logs without
    care, and get nonzero results. -/
theorem fast_products_converge {f : ℕ → ℂ → ℂ} {s : Set ℂ} {a c : ℝ} (o : IsOpen s)
    (c12 : c ≤ 1 / 2) (a0 : a ≥ 0) (a1 : a < 1) (h : ∀ n, AnalyticOn ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → abs (f n z - 1) ≤ c * a ^ n) :
    ∃ g : ℂ → ℂ, HasProdOn f g s ∧ AnalyticOn ℂ g s ∧ ∀ z, z ∈ s → g z ≠ 0 := by
  set fl := fun n z ↦ log (f n z)
  have near1 : ∀ n z, z ∈ s → abs (f n z - 1) ≤ 1 / 2 := by
    intro n z zs
    calc abs (f n z - 1)
      _ ≤ c * a ^ n := hf n z zs
      _ ≤ (1 / 2 : ℝ) * (1:ℝ) ^ n := by bound
      _ = 1 / 2 := by norm_num
  have near1' : ∀ n z, z ∈ s → abs (f n z - 1) < 1 := fun n z zs ↦
    lt_of_le_of_lt (near1 n z zs) (by linarith)
  have expfl : ∀ n z, z ∈ s → exp (fl n z) = f n z := by
    intro n z zs; refine' Complex.exp_log _
    exact near_one_avoids_zero (near1' n z zs)
  have hl : ∀ n, AnalyticOn ℂ (fl n) s := fun n ↦ log_analytic_near_one o (h n) (near1' n)
  set c2 := 2 * c
  have hfl : ∀ n z, z ∈ s → abs (fl n z) ≤ c2 * a ^ n := by
    intro n z zs
    calc abs (fl n z)
      _ = abs (log (f n z)) := rfl
      _ ≤ 2 * abs (f n z - 1) := (log_small (near1 n z zs))
      _ ≤ 2 * (c * a ^ n) := by linarith [hf n z zs]
      _ = 2 * c * a ^ n := by ring
      _ = c2 * a ^ n := rfl
  rcases fast_series_converge o a0 a1 hl hfl with ⟨gl, gla, us⟩
  set g := fun z ↦ exp (gl z)
  use g; refine' ⟨_, _, _⟩
  · intro z zs
    specialize us z zs; simp at us
    have comp :
      Filter.Tendsto (exp ∘ fun N : Finset ℕ ↦ N.sum fun n ↦ fl n z) atTop (𝓝 (exp (gl z))) :=
      Filter.Tendsto.comp (Continuous.tendsto Complex.continuous_exp _) us
    have expsum0 : (exp ∘ fun N : Finset ℕ ↦ N.sum fun n ↦ fl n z) = fun N : Finset ℕ ↦
        N.prod fun n ↦ f n z := by
      apply funext; intro N; simp; rw [Complex.exp_sum]; simp_rw [expfl _ z zs]
    rw [expsum0] at comp; assumption
  · exact fun z zs ↦ AnalyticAt.exp.comp (gla z zs)
  · simp only [Complex.exp_ne_zero, Ne.def, not_false_iff, imp_true_iff]

/-- Same as above, but converge to `tprodOn` -/
theorem fast_products_converge' {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (c12 : c ≤ 1 / 2) (a0 : 0 ≤ a) (a1 : a < 1) (h : ∀ n, AnalyticOn ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → abs (f n z - 1) ≤ c * a ^ n) :
    ProdExistsOn f s ∧ AnalyticOn ℂ (tprodOn f) s ∧ ∀ z, z ∈ s → tprodOn f z ≠ 0 := by
  rcases fast_products_converge o c12 a0 a1 h hf with ⟨g, gp, ga, g0⟩
  refine' ⟨_, _, _⟩; · exact fun z zs ↦ ⟨g z, gp z zs⟩
  · rwa [← analyticOn_congr o fun z zs ↦ (gp.tprodOn_eq z zs).symm]
  · intro z zs; rw [gp.tprodOn_eq z zs]; exact g0 z zs

/-- Powers commute with products -/
theorem product_pow {f : ℕ → ℂ} {g : ℂ} (p : ℕ) (h : HasProd f g) :
    HasProd (fun n ↦ f n ^ p) (g ^ p) := by
  rw [HasProd]; simp_rw [Finset.prod_pow]
  exact Filter.Tendsto.comp (Continuous.tendsto (continuous_pow p) g) h

/-- Powers commute with products (`tprod` version) -/
theorem product_pow' {f : ℕ → ℂ} {p : ℕ} (h : ProdExists f) :
    tprod f ^ p = tprod fun n ↦ f n ^ p := by
  rcases h with ⟨g, h⟩; rw [HasProd.tprod_eq h]; rw [HasProd.tprod_eq _]; exact product_pow p h

/-- Adding one more term to a product multiplies by it -/
theorem product_cons {a g : ℂ} {f : ℕ → ℂ} (h : HasProd f g) :
    HasProd (Stream'.cons a f) (a * g) := by
  rw [HasProd] at h ⊢
  have ha := Filter.Tendsto.comp (Continuous.tendsto (continuous_mul_left a) g) h
  have s : ((fun z ↦ a * z) ∘ fun N : Finset ℕ ↦ N.prod f) =
      (fun N : Finset ℕ ↦ N.prod (Stream'.cons a f)) ∘ push := by
    apply funext; intro N; simp; exact push_prod
  rw [s] at ha
  exact tendsto_comp_push.mp ha

/-- Adding one more term to a product multiplies by it (`tprod` version) -/
theorem product_cons' {a : ℂ} {f : ℕ → ℂ} (h : ProdExists f) :
    tprod (Stream'.cons a f) = a * tprod f := by
  rcases h with ⟨g, h⟩; rw [HasProd.tprod_eq h]; rw [HasProd.tprod_eq _]; exact product_cons h

/-- Dropping a nonzero term divides by it -/
theorem product_drop {f : ℕ → ℂ} {g : ℂ} (f0 : f 0 ≠ 0) (h : HasProd f g) :
    HasProd (fun n ↦ f (n + 1)) (g / f 0) := by
  have c := @product_cons (f 0)⁻¹ _ _ h
  rw [HasProd]
  rw [inv_mul_eq_div, HasProd, ← tendsto_comp_push, ← tendsto_comp_push] at c
  have s : ((fun N : Finset ℕ ↦ N.prod fun n ↦ (Stream'.cons (f 0)⁻¹ f) n) ∘ push) ∘ push =
      fun N : Finset ℕ ↦ N.prod fun n ↦ f (n + 1) := by
    clear c h g; apply funext; intro N; simp
    nth_rw 2 [← Stream'.eta f]
    simp only [←push_prod, Stream'.head, Stream'.tail, Stream'.nth, ←mul_assoc, inv_mul_cancel f0,
      one_mul]
  rw [s] at c; assumption

/-- Dropping a nonzero term divides by it (`tprod` version) -/
theorem product_drop' {f : ℕ → ℂ} (f0 : f 0 ≠ 0) (h : ProdExists f) :
    (tprod fun n ↦ f (n + 1)) = tprod f / f 0 := by
  rcases h with ⟨g, h⟩; rw [HasProd.tprod_eq h]; rw [HasProd.tprod_eq _]; exact product_drop f0 h

/-- Products that start with zero are zero -/
theorem product_head_zero {f : ℕ → ℂ} (f0 : f 0 = 0) : HasProd f 0 := by
  rw [HasProd]; rw [Metric.tendsto_atTop]; intro e ep
  use Finset.range 1; intro N N1
  simp at N1; rw [Finset.prod_eq_zero N1 f0]; simpa

/-- Separate out head and tail in a product -/
theorem product_split {f : ℕ → ℂ} (h : ProdExists f) : tprod f = f 0 * tprod fun n ↦ f (n + 1) := by
  by_cases f0 : f 0 = 0; · rw [f0, (product_head_zero f0).tprod_eq]; simp
  rw [product_drop' f0 h]; field_simp; exact mul_comm _ _

/-- The zero product -/
theorem HasProd.zero : HasProd (fun _ ↦ 0) 0 := by apply product_head_zero; rfl
