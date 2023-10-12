/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.branch.GeoffreyIrving.Ray.AnalyticManifold.AnalyticManifold
import Mathlib.branch.GeoffreyIrving.Ray.Tactic.Bound

/-!
## Special properties of 1D complex manifolds

One complex dimension is special, and 1D complex manifolds inherit this specialness.

Unfortunately, a lot of proofs here are messy, as we abuse the definitional quality
of `TangentSpace I z = ℂ` to do noncanonical field arithmetic over `ℂ`.
-/

open Filter (eventually_of_forall Tendsto)
open Function (uncurry)
open Set
open scoped Manifold Topology
noncomputable section

namespace OneDimension

/-- Abbreviation for `𝓘(ℂ,ℂ) = modelWithCornersSelf ℂ ℂ` -/
notation "I" => modelWithCornersSelf ℂ ℂ

/-- Abbreviation for `𝓘(ℂ,ℂ).prod 𝓘(ℂ,ℂ)` -/
notation "II" => ModelWithCorners.prod I I

end OneDimension

open OneDimension

variable {S : Type} [TopologicalSpace S] [cs : ChartedSpace ℂ S] [AnalyticManifold I S]
variable {T : Type} [TopologicalSpace T] [ct : ChartedSpace ℂ T] [AnalyticManifold I T]
variable {U : Type} [TopologicalSpace U] [cu : ChartedSpace ℂ U] [AnalyticManifold I U]

/-- 1D tangent spaces are nontrivial -/
instance one_dimension_tangentSpace_nontrivial (z : S) : Nontrivial (TangentSpace I z) := by
  simp only [TangentSpace]; infer_instance

/-- 1D tangent spaces are `NormedAddCommGroup`s -/
instance oneDimensionTangentSpaceNormedAddCommGroup (z : S) :
    NormedAddCommGroup (TangentSpace I z) := by
  simp only [TangentSpace]; infer_instance

/-- 1D tangent spaces are `NormedSpace`s -/
instance oneDimensionTangentSpaceNormedSpace (z : S) : NormedSpace ℂ (TangentSpace I z) := by
  simp only [TangentSpace]; infer_instance

/-- The tangent space norm is `abs`, if we unpack types -/
theorem tangentSpace_norm_eq_complex_norm (z : S) (x : TangentSpace I z) : ‖x‖ = Complex.abs x := by
  rw [← Complex.norm_eq_abs]

/-- 1D tangent space maps are (noncanonically!) equivalent to `ℂ` (linear equivalence) -/
def mderivToScalar' (z : S) (w : T) : (TangentSpace I z →L[ℂ] TangentSpace I w) ≃ₗ[ℂ] ℂ where
  toFun := by intro x; have y : ℂ →L[ℂ] ℂ := x; exact y 1
  invFun := by intro x; have y : ℂ →L[ℂ] ℂ := x • ContinuousLinearMap.id ℂ ℂ; exact y
  map_add' x y := ContinuousLinearMap.add_apply _ _ _
  map_smul' s x := by
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
  left_inv := by
    intro x; simp only; apply ContinuousLinearMap.ext; intro s
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [mul_comm, ← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
  right_inv := by
    intro x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]

/-- 1D tangent space maps are (noncanonically!) equivalent to `ℂ` (continuous linear equivalence) -/
def mderivToScalar (z : S) (w : T) : (TangentSpace I z →L[ℂ] TangentSpace I w) ≃L[ℂ] ℂ where
  toLinearEquiv := mderivToScalar' z w
  continuous_toFun := by
    simp only [mderivToScalar']
    rw [Metric.continuous_iff]; intro x e ep; use e / 2, half_pos ep; intro y xy
    simp only [dist_eq_norm, ← ContinuousLinearMap.sub_apply y x (1 : ℂ)] at xy ⊢
    have b := ContinuousLinearMap.le_of_op_norm_le _ xy.le (1 : ℂ)
    simp only [tangentSpace_norm_eq_complex_norm, Complex.abs.map_one, mul_one] at b ⊢
    exact lt_of_le_of_lt b (half_lt_self ep)
  continuous_invFun := by
    simp only [mderivToScalar']
    rw [Metric.continuous_iff]; intro x e ep; use e / 2, half_pos ep; intro y xy
    simp only [dist_eq_norm, Complex.norm_eq_abs] at xy ⊢
    refine' lt_of_le_of_lt _ (half_lt_self ep)
    apply ContinuousLinearMap.op_norm_le_bound' _ (half_pos ep).le; intro s _
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply]
    simp only [ContinuousLinearMap.id_apply, tangentSpace_norm_eq_complex_norm, smul_eq_mul,
      ←mul_sub_right_distrib, Complex.abs.map_mul] at xy ⊢
    bound

/-- Given nonzero `u`, a tangent space map `x` is `0` iff `x u = 0` -/
theorem mderiv_eq_zero_iff {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (u : TangentSpace I z) : f u = 0 ↔ f = 0 ∨ u = 0 := by
  constructor
  · rw [or_iff_not_imp_right]; intro f0 u0
    apply ContinuousLinearMap.ext; intro v
    simp only [TangentSpace] at f u v u0
    have e : v = (v * u⁻¹) • u := by simp only [smul_eq_mul, mul_assoc, inv_mul_cancel u0, mul_one]
    rw [ContinuousLinearMap.zero_apply, e, f.map_smul, f0, smul_zero]
  · intro h; cases' h with h h
    simp only [h, ContinuousLinearMap.zero_apply]
    simp only [h, ContinuousLinearMap.map_zero]

/-- Given nonzero `u`, a tangent space map `x` is `0` iff `x u = 0` -/
theorem mderiv_eq_zero_iff' {z : S} {w : T} {f : TangentSpace I z →L[ℂ] TangentSpace I w}
    {u : TangentSpace I z} (u0 : u ≠ 0) : f u = 0 ↔ f = 0 := by
  simp only [mderiv_eq_zero_iff, u0, or_false_iff]

/-- Given nonzero `u`, a tangent space map `x` is `≠ 0` iff `x u ≠ 0` -/
theorem mderiv_ne_zero_iff {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (u : TangentSpace I z) : f u ≠ 0 ↔ f ≠ 0 ∧ u ≠ 0 := by
  simp only [← not_or]; exact Iff.not (mderiv_eq_zero_iff _ _)

/-- Given nonzero `u`, a tangent space map `x` is `≠ 0` iff `x u ≠ 0` -/
theorem mderiv_ne_zero_iff' {z : S} {w : T} {f : TangentSpace I z →L[ℂ] TangentSpace I w}
    {u : TangentSpace I z} (u0 : u ≠ 0) : f u ≠ 0 ↔ f ≠ 0 := by
  simp only [ne_eq, mderiv_ne_zero_iff, u0, not_false_eq_true, and_true]

/-- 1D map composition is zero iff either side is -/
theorem mderiv_comp_eq_zero_iff {x : S} {y : T} {z : U}
    (f : TangentSpace I y →L[ℂ] TangentSpace I z) (g : TangentSpace I x →L[ℂ] TangentSpace I y) :
    f.comp g = 0 ↔ f = 0 ∨ g = 0 := by
  rcases exists_ne (0 : TangentSpace I x) with ⟨t, t0⟩
  constructor
  · intro h; simp only [← mderiv_eq_zero_iff' t0, ContinuousLinearMap.comp_apply] at h
    by_cases g0 : g t = 0
    right; rw [mderiv_eq_zero_iff' t0] at g0; exact g0
    left; rwa [← mderiv_eq_zero_iff' g0]
  · intro h; cases' h with h h; simp only [h, g.zero_comp]; simp only [h, f.comp_zero]

/-- 1D map composition is nonzero if both sides are -/
theorem mderiv_comp_ne_zero {x : S} {y : T} {z : U} (f : TangentSpace I y →L[ℂ] TangentSpace I z)
    (g : TangentSpace I x →L[ℂ] TangentSpace I y) : f ≠ 0 → g ≠ 0 → f.comp g ≠ 0 := by
  intro f0 g0; simp only [Ne.def, mderiv_comp_eq_zero_iff, f0, g0, or_self_iff, not_false_iff]

/-- Nonzero `mfderiv` implies differentiability -/
theorem has_mfderiv_at_of_mderiv_ne_zero {f : S → T} {x : S} (d0 : mfderiv I I f x ≠ 0) :
    MDifferentiableAt I I f x := by
  contrapose d0
  simp only [mfderiv, d0, if_false, Ne.def, eq_self_iff_true, not_true, not_false_iff]

/-- If two functions have nonzero derivative, their composition has nonzero derivative -/
theorem mderiv_comp_ne_zero' {f : T → U} {g : S → T} {x : S} :
    mfderiv I I f (g x) ≠ 0 → mfderiv I I g x ≠ 0 → mfderiv I I (fun x ↦ f (g x)) x ≠ 0 := by
  intro df dg
  have e : (fun x ↦ f (g x)) = f ∘ g := rfl
  rw [e, mfderiv_comp x (has_mfderiv_at_of_mderiv_ne_zero df) (has_mfderiv_at_of_mderiv_ne_zero dg)]
  exact mderiv_comp_ne_zero _ _ df dg

/-- Nonzero 1D derivatives are invertible -/
def mderivEquiv {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w) (f0 : f ≠ 0) :
    TangentSpace I z ≃L[ℂ] TangentSpace I w where
  toFun := f
  map_add' := f.map_add'
  map_smul' := f.map_smul'
  invFun := by
    intro x; have f' : ℂ →L[ℂ] ℂ := f; simp only [TangentSpace] at f x; exact (f' 1)⁻¹ * x
  left_inv := by
    generalize hu : (1:ℂ) = u
    have u0 : u ≠ 0 := by rw [←hu]; norm_num
    have h := mderiv_ne_zero_iff' (f := f) (u := (u : TangentSpace I z)) u0
    intro x; simp only [TangentSpace] at f x ⊢
    have e : f x = (f u) * x := by
      rw [mul_comm, ← smul_eq_mul, ← f.map_smul, smul_eq_mul, ←hu, mul_one]
    simp only [e, ← mul_assoc, inv_mul_cancel, one_mul]; rw [inv_mul_cancel, one_mul]; rwa [h]
  right_inv := by
    generalize hu : (1:ℂ) = u
    have u0 : u ≠ 0 := by rw [←hu]; norm_num
    have h := mderiv_ne_zero_iff' (f := f) (u := (u : TangentSpace I z)) u0
    intro x; simp only [TangentSpace] at f x ⊢
    have e : ∀ y : ℂ, f y = (f u) * y := by
      intro y; rw [mul_comm, ← smul_eq_mul, ← f.map_smul, smul_eq_mul, ←hu, mul_one]
    rw [e ((f u)⁻¹ * x), ← mul_assoc, mul_inv_cancel, one_mul]; rwa [h]
  continuous_toFun := f.cont
  continuous_invFun := by
    simp only [TangentSpace] at f ⊢; exact Continuous.mul continuous_const continuous_id

theorem mderivEquiv_apply {z : S} {w : T} {f : TangentSpace I z →L[ℂ] TangentSpace I w} (f0 : f ≠ 0)
    (x : TangentSpace I z) : mderivEquiv f f0 x = f x := rfl

theorem mderivEquiv_eq {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w) (f0 : f ≠ 0) :
    ↑(mderivEquiv f f0) = f := by apply ContinuousLinearMap.ext; intro x; rfl

/-- Chart derivatives are nonzero -/
theorem extChartAt_mderiv_ne_zero' {z w : S} (m : w ∈ (extChartAt I z).source) :
    mfderiv I I (extChartAt I z) w ≠ 0 := by
  rcases exists_ne (0 : TangentSpace I z) with ⟨t, t0⟩
  rw [← mderiv_ne_zero_iff' t0]; contrapose t0; simp only [not_not] at t0 ⊢
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_left_inverse m) t
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_zero,
    ContinuousLinearMap.id_apply] at h
  rw [←h, ContinuousLinearMap.apply_eq_zero_of_eq_zero]; exact t0

/-- Chart derivatives are nonzero -/
theorem extChartAt_symm_mderiv_ne_zero' {z : S} {w : ℂ} (m : w ∈ (extChartAt I z).target) :
    mfderiv I I (extChartAt I z).symm w ≠ 0 := by
  rcases exists_ne (0 : TangentSpace I (extChartAt I z z)) with ⟨t, t0⟩
  rw [← mderiv_ne_zero_iff' t0]; contrapose t0; simp only [not_not] at t0 ⊢
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_right_inverse m) t
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_zero,
    ContinuousLinearMap.id_apply] at h
  rw [←h, ContinuousLinearMap.apply_eq_zero_of_eq_zero]; exact t0

/-- Chart derivatives are nonzero -/
theorem extChartAt_mderiv_ne_zero (z : S) : mfderiv I I (extChartAt I z) z ≠ 0 :=
  extChartAt_mderiv_ne_zero' (mem_extChartAt_source I z)

/-- Chart derivatives are nonzero -/
theorem extChartAt_symm_mderiv_ne_zero (z : S) :
    mfderiv I I (extChartAt I z).symm (extChartAt I z z) ≠ 0 :=
  extChartAt_symm_mderiv_ne_zero' (mem_extChartAt_target I z)

/-- Identity derivatives are nonzero -/
theorem id_mderiv_ne_zero {z : S} : mfderiv I I (fun z ↦ z) z ≠ 0 := by
  have d : MDifferentiableAt I I (fun z ↦ z) z := mdifferentiableAt_id I
  simp only [mfderiv, d, if_true, writtenInExtChartAt, Function.comp,
    ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  have e : (fun w ↦ extChartAt I z ((extChartAt I z).symm w)) =ᶠ[𝓝 (extChartAt I z z)] id := by
    apply ((extChartAt_open_target I z).eventually_mem (mem_extChartAt_target I z)).mp
    refine' eventually_of_forall fun w m ↦ _
    simp only [id, LocalEquiv.right_inv _ m]
  simp only [e.fderiv_eq, fderiv_id, Ne.def, ContinuousLinearMap.ext_iff, not_forall,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply]
  use 1, one_ne_zero

/-- Nonzeroness of `mfderiv` reduces to nonzeroness of `deriv` -/
theorem mfderiv_eq_zero_iff_deriv_eq_zero {f : ℂ → ℂ} {z : ℂ} :
    mfderiv I I f z = 0 ↔ deriv f z = 0 := by
  by_cases d : DifferentiableAt ℂ f z
  · constructor
    · have h := d.mdifferentiableAt.hasMFDerivAt; intro e; rw [e] at h
      have p := h.hasFDerivAt.hasDerivAt
      simp only [ContinuousLinearMap.zero_apply] at p; exact p.deriv
    · have h := d.hasDerivAt; intro e; rw [e] at h
      have s0 : (1 : ℂ →L[ℂ] ℂ).smulRight (0 : ℂ) = 0 := by
        apply ContinuousLinearMap.ext
        simp only [ContinuousLinearMap.smulRight_apply, Algebra.id.smul_eq_mul,
          MulZeroClass.mul_zero, ContinuousLinearMap.zero_apply, forall_const]
      have p := h.hasFDerivAt.hasMFDerivAt; rw [s0] at p; exact p.mfderiv
  · have d' : ¬MDifferentiableAt I I f z := by
      contrapose d; simp only [not_not] at d ⊢; exact d.differentiableAt
    simp only [deriv_zero_of_not_differentiableAt d, mfderiv_zero_of_not_mdifferentiableAt d',
      eq_self_iff_true]

/-- `mfderiv ≠ 0` iff `deriv ≠ 0` -/
theorem mfderiv_ne_zero_iff_deriv_ne_zero {f : ℂ → ℂ} {z : ℂ} :
    mfderiv I I f z ≠ 0 ↔ deriv f z ≠ 0 := by rw [not_iff_not, mfderiv_eq_zero_iff_deriv_eq_zero]

/-- A critical point is where the derivative of `f` vanishes -/
def Critical (f : S → T) (z : S) :=
  mfderiv I I f z = 0

/-- A precritical point is an iterated preimage of a critical point -/
def Precritical (f : S → S) (z : S) :=
  ∃ n, Critical f (f^[n] z)

/-- Critical points of iterations are precritical points -/
theorem critical_iter {f : S → S} {n : ℕ} {z : S} (fa : Holomorphic I I f) (c : Critical f^[n] z) :
    Precritical f z := by
  induction' n with n h
  · rw [Function.iterate_zero, Critical, mfderiv_id, ← ContinuousLinearMap.op_norm_zero_iff,
      ContinuousLinearMap.norm_id] at c
    norm_num at c
  · rw [Function.iterate_succ', Critical,
      mfderiv_comp z (fa _).mdifferentiableAt (fa.iter _ _).mdifferentiableAt,
      mderiv_comp_eq_zero_iff] at c
    cases' c with c c; use n, c; exact h c

/-!
## Facts about `mfderiv` related to continuity and holomorphicity

These facts would ideally follow from continuity and holomorphicity of `mfderiv`, but we can't
express that directly as `mfderiv` lives in a different type at each point.  Rather than detour
into the necessary theory, I'm going to express what I need in coordinates for now.
-/

/-- A curried function in coordinates -/
def inChart (f : ℂ → S → T) (c : ℂ) (z : S) : ℂ → ℂ → ℂ := fun e w ↦
  extChartAt I (f c z) (f e ((extChartAt I z).symm w))

/-- `inChart` is analytic -/
theorem HolomorphicAt.inChart {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : HolomorphicAt II I (uncurry f) (c, z)) :
    AnalyticAt ℂ (uncurry (inChart f c z)) (c, _root_.extChartAt I z z) := by
  apply HolomorphicAt.analyticAt II I
  apply (HolomorphicAt.extChartAt (mem_extChartAt_source I (f c z))).comp_of_eq
  apply fa.curry_comp_of_eq holomorphicAt_fst
  apply (HolomorphicAt.extChartAt_symm (mem_extChartAt_target I z)).comp_of_eq holomorphicAt_snd
  repeat' simp only [LocalEquiv.left_inv _ (mem_extChartAt_source I z)]

/-- `inChart` preserves critical points locally -/
theorem inChart_critical {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : HolomorphicAt II I (uncurry f) (c, z)) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, z),
      mfderiv I I (f p.1) p.2 = 0 ↔ deriv (inChart f c z p.1) (extChartAt I z p.2) = 0 := by
  apply (fa.continuousAt.eventually_mem (isOpen_extChartAt_source I (f c z))
    (mem_extChartAt_source I (f c z))).mp
  apply ((isOpen_extChartAt_source II (c, z)).eventually_mem (mem_extChartAt_source _ _)).mp
  refine' fa.eventually.mp (eventually_of_forall _); intro ⟨e, w⟩ fa m fm
  simp only [extChartAt_prod, LocalEquiv.prod_source, extChartAt_eq_refl, LocalEquiv.refl_source,
    mem_prod, mem_univ, true_and_iff] at m
  simp only [uncurry] at fm
  have m' := LocalEquiv.map_source _ m
  simp only [← mfderiv_eq_zero_iff_deriv_eq_zero]
  simp only [inChart]
  have cd : HolomorphicAt I I (extChartAt I (f c z)) (f e w) := HolomorphicAt.extChartAt fm
  have fd : HolomorphicAt I I (f e ∘ (extChartAt I z).symm) (extChartAt I z w) := by
    simp only [Function.comp]
    exact HolomorphicAt.comp_of_eq fa.in2 (HolomorphicAt.extChartAt_symm m')
      (LocalEquiv.right_inv _ m)
  have ce : (fun w ↦ extChartAt I (f c z) (f e ((extChartAt I z).symm w))) =
      extChartAt I (f c z) ∘ f e ∘ (extChartAt I z).symm := rfl
  rw [ce, mfderiv_comp_of_eq cd.mdifferentiableAt fd.mdifferentiableAt ?blah,
    mfderiv_comp_of_eq fa.in2.mdifferentiableAt
      (HolomorphicAt.extChartAt_symm m').mdifferentiableAt]
  · simp only [mderiv_comp_eq_zero_iff, Function.comp]
    rw [(extChartAt I z).left_inv m]
    simp only [extChartAt_mderiv_ne_zero' fm, false_or]
    constructor
    · intro h; left; exact h
    · intro h; cases' h with h h; exact h; simpa only using extChartAt_symm_mderiv_ne_zero' m' h
  · exact LocalEquiv.left_inv _ m
  · simp only [Function.comp, LocalEquiv.left_inv _ m]

/-- `mfderiv` is nonzero near where it is nonzero (parameterized version) -/
theorem mfderiv_ne_zero_eventually' {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : HolomorphicAt II I (uncurry f) (c, z)) (f0 : mfderiv I I (f c) z ≠ 0) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, z), mfderiv I I (f p.1) p.2 ≠ 0 := by
  set g := inChart f c z
  have g0 := inChart_critical fa
  have g0n : ∀ᶠ p : ℂ × S in 𝓝 (c, z), deriv (g p.1) (extChartAt I z p.2) ≠ 0 := by
    refine' ContinuousAt.eventually_ne _ _
    · have e : (fun p : ℂ × S ↦ deriv (g p.1) (extChartAt I z p.2)) =
        (fun p : ℂ × ℂ ↦ deriv (g p.1) p.2) ∘ fun p : ℂ × S ↦ (p.1, extChartAt I z p.2) := rfl
      rw [e]
      exact fa.inChart.deriv2.continuousAt.comp_of_eq
        (continuousAt_fst.prod ((continuousAt_extChartAt I z).comp_of_eq continuousAt_snd rfl))
        rfl
    · contrapose f0; simp only [not_not, Function.comp] at f0 ⊢; rw [g0.self]; exact f0
  refine' g0.mp (g0n.mp (eventually_of_forall fun w g0 e ↦ _))
  rw [Ne.def, e]; exact g0

/-- `mfderiv` is nonzero near where it is nonzero -/
theorem mfderiv_ne_zero_eventually {f : S → T} {z : S} (fa : HolomorphicAt I I f z)
    (f0 : mfderiv I I f z ≠ 0) : ∀ᶠ w in 𝓝 z, mfderiv I I f w ≠ 0 := by
  set c : ℂ := 0
  set g : ℂ → S → T := fun _ z ↦ f z
  have ga : HolomorphicAt II I (uncurry g) (c, z) := by
    have e : uncurry g = f ∘ fun p ↦ p.2 := rfl; rw [e]
    apply HolomorphicAt.comp_of_eq fa holomorphicAt_snd; simp only
  have pc : Tendsto (fun z ↦ (c, z)) (𝓝 z) (𝓝 (c, z)) := continuousAt_const.prod continuousAt_id
  exact pc.eventually (mfderiv_ne_zero_eventually' ga f0)

/-- The set of noncritical points is open -/
theorem isOpen_noncritical {f : ℂ → S → T} (fa : Holomorphic II I (uncurry f)) :
    IsOpen {p : ℂ × S | ¬Critical (f p.1) p.2} := by
  rw [isOpen_iff_eventually]; intro ⟨c, z⟩ m; exact mfderiv_ne_zero_eventually' (fa _) m

/-- The set of critical points is closed -/
theorem isClosed_critical {f : ℂ → S → T} (fa : Holomorphic II I (uncurry f)) :
    IsClosed {p : ℂ × S | Critical (f p.1) p.2} := by
  have c := (isOpen_noncritical fa).isClosed_compl
  simp only [compl_setOf, not_not] at c; exact c

/-- Osgood's theorem on 2D product manifolds: separate analyticity + continuity
    implies joint analyticity.  I'm not sure if a Hartogs' analogue is possible,
    since we use continuity to remain within the right charts. -/
theorem osgoodManifold {f : S × T → U} (fc : Continuous f)
    (f0 : ∀ x y, HolomorphicAt I I (fun x ↦ f (x, y)) x)
    (f1 : ∀ x y, HolomorphicAt I I (fun y ↦ f (x, y)) y) : Holomorphic II I f := by
  rw [holomorphic_iff]; use fc; intro p; apply osgood_at'
  have fm : ∀ᶠ q in 𝓝 (extChartAt II p p),
      f ((extChartAt II p).symm q) ∈ (extChartAt I (f p)).source := by
    refine ContinuousAt.eventually_mem (fc.continuousAt.comp (continuousAt_extChartAt_symm II p))
        (isOpen_extChartAt_source I (f p)) ?_
    rw [Function.comp, (extChartAt II p).left_inv (mem_extChartAt_source _ _)]
    apply mem_extChartAt_source
  apply ((extChartAt_open_target II p).eventually_mem (mem_extChartAt_target II p)).mp
  refine' fm.mp (eventually_of_forall fun q fm m ↦ ⟨_, _, _⟩)
  · exact (continuousAt_extChartAt' I _ fm).comp_of_eq
        (fc.continuousAt.comp (continuousAt_extChartAt_symm'' _ _ m)) rfl
  · apply HolomorphicAt.analyticAt I I
    refine' (HolomorphicAt.extChartAt fm).comp_of_eq _ rfl
    rw [extChartAt_prod] at m
    simp only [Function.comp, extChartAt_prod, LocalEquiv.prod_symm, LocalEquiv.prod_coe,
      LocalEquiv.prod_target, mem_prod_eq] at m ⊢
    exact (f0 _ _).comp (HolomorphicAt.extChartAt_symm m.1)
  · apply HolomorphicAt.analyticAt I I
    refine' (HolomorphicAt.extChartAt fm).comp_of_eq _ rfl
    rw [extChartAt_prod] at m
    simp only [Function.comp, extChartAt_prod, LocalEquiv.prod_symm, LocalEquiv.prod_coe,
      LocalEquiv.prod_target, mem_prod_eq] at m ⊢
    exact (f1 _ _).comp (HolomorphicAt.extChartAt_symm m.2)
