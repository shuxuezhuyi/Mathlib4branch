/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
-- fun x, max b (log x)
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.branch.GeoffreyIrving.Ray.Tactic.Bound

/-!
## `x ↦ max b (log x)`

We define `maxLog b x = max b (log x)` and enumerate its properties.  This function is useful in
proving properties of analytic functions using subharmonic functions, as it lets us avoid working
over the extended reals.  `log (f z)` is subharmonic if `f z` is analytic, but `= -∞` at zeroes of
`f`.  `maxLog b (f z)` is similarly subharmonic, but stays finite.
-/

open Complex (abs)
open scoped Real
open Set (univ Ici)
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `max b (log x)` -/
def maxLog (b x : ℝ) : ℝ :=
  (max b.exp x).log

theorem max_exp_pos {b x : ℝ} : 0 < max b.exp x :=
  lt_of_lt_of_le (Real.exp_pos _) (by bound)

@[simp]
theorem le_maxLog (b x : ℝ) : b ≤ maxLog b x := by
  rw [maxLog, Real.le_log_iff_exp_le max_exp_pos]; bound

theorem maxLog_eq_b {b x : ℝ} (h : x ≤ b.exp) : maxLog b x = b := by simp [maxLog, max_eq_left h]

theorem maxLog_eq_log {b x : ℝ} (h : b.exp ≤ x) : maxLog b x = x.log := by
  simp [maxLog, max_eq_right h]

theorem maxLog_le {b x y : ℝ} (yb : b ≤ y) (xy : x ≤ y.exp) : maxLog b x ≤ y := by
  rw [maxLog, Real.log_le_iff_le_exp max_exp_pos]; apply max_le
  apply Real.exp_le_exp.mpr yb; exact xy

theorem le_exp_maxLog (b x : ℝ) : x ≤ (maxLog b x).exp := by
  rw [maxLog, Real.exp_log max_exp_pos]; bound

/-- Extract underlying bounds from `maxLog` bounds -/
theorem le_of_maxLog_le {b x y : ℝ} (m : maxLog b x ≤ y) : x ≤ y.exp := by
  rw [maxLog, Real.log_le_iff_le_exp max_exp_pos] at m; exact le_of_max_le_right m

/-- `maxLog` is increasing -/
theorem monotone_maxLog (b : ℝ) : Monotone fun x ↦ maxLog b x := by
  simp_rw [maxLog]; intro x y xy
  simp only [ge_iff_le]; rw [Real.log_le_log max_exp_pos max_exp_pos]
  apply max_le_max (le_refl _) xy

/-- `maxLog` is continuous -/
theorem continuous_maxLog (b : ℝ) : Continuous fun x ↦ maxLog b x := by
  simp_rw [maxLog]; rw [continuous_iff_continuousAt]; intro x
  refine (ContinuousAt.log ?_ max_exp_pos.ne').comp ?_
  · apply Continuous.continuousAt; apply Continuous.max; exact continuous_const; exact continuous_id
  · exact continuousAt_id

/-- `max b (log ‖f z‖)` is continuous for continuous `f` -/
theorem ContinuousOn.maxLog_norm {f : ℂ → E} {s : Set ℂ} (fc : ContinuousOn f s) (b : ℝ) :
    ContinuousOn (fun z ↦ maxLog b ‖f z‖) s :=
  (continuous_maxLog b).comp_continuousOn fc.norm

/-- `log` is Lipschitz away from 0 -/
theorem LipschitzOnWith.log (b : ℝ) : LipschitzOnWith (-b).exp.toNNReal Real.log (Ici b.exp) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  have half : ∀ x y : ℝ, b.exp ≤ y → y ≤ x → |x.log - y.log| ≤ (-b).exp * |x - y| := by
    intro x y yb xy
    have yp : y > 0 := lt_of_lt_of_le (Real.exp_pos _) yb
    have xp : x > 0 := lt_of_lt_of_le yp xy
    have yi : y⁻¹ ≤ (-b).exp := by rw [Real.exp_neg]; bound
    rw [abs_of_nonneg (sub_nonneg.mpr xy)]
    rw [abs_of_nonneg (sub_nonneg.mpr ((Real.log_le_log yp xp).mpr xy))]
    rw [← Real.log_div xp.ne' yp.ne']
    rw [Real.log_le_iff_le_exp (div_pos xp yp)]
    trans (y⁻¹ * (x - y)).exp; swap; bound
    have e : y⁻¹ * (x - y) = x / y - 1 := by field_simp [yp.ne']
    rw [e]
    have e1 := Real.add_one_le_exp (x / y - 1)
    simp at e1; exact e1
  intro x xs y ys
  simp at xs ys ⊢
  rw [max_eq_left (Real.exp_pos _).le]
  simp_rw [Real.dist_eq]
  by_cases xy : x ≥ y; · exact half x y ys xy
  simp at xy
  rw [← neg_sub y x, abs_neg]
  rw [← neg_sub y.log x.log, abs_neg]
  exact half y x xs xy.le

/-- `maxLog` is Lipschitz -/
theorem LipschitzWith.maxLog (b : ℝ) : LipschitzWith (-b).exp.toNNReal (maxLog b) := by
  rw [← lipschitzOn_univ]
  have h := (LipschitzOnWith.log b).comp ((LipschitzWith.id.const_max b.exp).lipschitzOnWith univ)
    (by simp only [id_eq, ge_iff_le, Set.maps_univ_to, Set.mem_Ici, le_max_iff, le_refl, true_or,
      forall_const])
  have e : Real.log ∘ max (Real.exp b) = _root_.maxLog b := by funext x; simp [_root_.maxLog]
  simpa only [e, mul_one, id_eq, ge_iff_le, lipschitzOn_univ] using h
