/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.branch.GeoffreyIrving.Ray.Misc.Connected

/-!
## Continuation of a function from a convex set to its closure

We give an abstract version of "analytic continuation" from a convex set to its compact closure,
assuming that local continuation is possible at each boundary point.  We do not refer to analytic
functions directly at all: instead we speak of functions which everywhere satisfy a predicate
`p : (E → S) → E → Prop` where `E` is a normed space and `α : Type`.

Convexity is used only to guarantee a "good open cover" in the sense of
https://ncatlab.org/nlab/show/good+open+cover: a family of neighborhoods such that intersections
of neighborhoods are contractable.  Since our base set `s` is convex, we can use balls as good
neighborhoods, and all intersections are convex and thus contractable.

It would be better to define good neighborhoods directly and show that nice spaces have them,
but this may require a lot of machinery to cover manifolds in particular: the nLab page uses
the existence of Riemannian metrics.
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Classical
open Metric (ball isOpen_ball mem_ball mem_ball_self)
open Set
open scoped Real Topology
noncomputable section

-- Continuation of a functional equation from an open convex set to its closure
section Continuation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : Type} {p : (E → α) → E → Prop} {s : Set E} {f : E → α} {z : E}

/-- Information we need to continue a function from a convex set `s` to `closure s`, while
    preserving local properties of the function.  Such properties are represented by an abstract
    `p : (E → α) → E → Prop`, where `p f x` means `f` is a valid germ at `x`. -/
structure Base (p : (E → α) → E → Prop) (s : Set E) (f : E → α) : Prop where
  /-- The base set is convex -/
  convex : Convex ℝ s
  /-- Its closure is compact, so that we can stitch together finitely many local continuations -/
  compact : IsCompact (closure s)
  /-- `p f x` is a local property of `f` near `x` -/
  congr : ∀ {f g x}, p f x → f =ᶠ[𝓝 x] g → p g x
  /-- `f` is valid near each `x ∈ s` -/
  start : ∀ᶠ x in 𝓝ˢ s, p f x
  /-- Given `x ∈ closure s`, we can continue `f` to a neighorhood of `x` -/
  point : ∀ {x}, x ∈ closure s → ∃ g, (∀ᶠ z in 𝓝 x, p g z) ∧ ∃ᶠ z in 𝓝 x, z ∈ s ∧ g z = f z
  /-- If `f0, f1` are valid on an open preconnected set, and match somewhere,
      they match everywhere -/
  unique : ∀ {f0 f1 : E → α} {t : Set E}, IsOpen t → IsPreconnected t →
    (∀ x, x ∈ t → p f0 x) → (∀ x, x ∈ t → p f1 x) → (∃ x, x ∈ t ∧ f0 x = f1 x) → EqOn f0 f1 t

/-- There is a ball around each `x ∈ closure s` with an associated defined `g` -/
lemma Base.ball (b : Base p s f) (x : closure s) :
    ∃ g r, 0 < r ∧ (∀ z, z ∈ ball (x : E) r → p g z) ∧ g =ᶠ[𝓝ˢ (s ∩ ball (x : E) r)] f := by
  rcases x with ⟨x, m⟩; simp only [Subtype.coe_mk]
  rcases b.point m with ⟨g, pg, e⟩
  rcases Metric.eventually_nhds_iff_ball.mp pg with ⟨r, rp, pg⟩
  rcases Filter.frequently_iff.mp e (Metric.ball_mem_nhds _ rp) with ⟨y, yb, ys, e⟩
  use g, r, rp, fun z zr ↦ pg z zr
  simp only [Filter.EventuallyEq, Filter.eventually_iff, mem_nhdsSet_iff_forall]
  intro z ⟨zs, zr⟩; simp only [← Filter.eventually_iff]
  have n : {z | p g z ∧ p f z} ∈ 𝓝ˢ (s ∩ Metric.ball x r) := by
    refine Filter.inter_mem ?_ ?_
    · exact nhdsSet_mono (inter_subset_right _ _)
        (Filter.mem_of_superset (mem_nhdsSet_self isOpen_ball) pg)
    · exact nhdsSet_mono (inter_subset_left _ _) b.start
  rcases local_preconnected_nhdsSet (b.convex.inter (convex_ball _ _)).isPreconnected n with
    ⟨u, uo, iu, up, uc⟩
  have eq := b.unique uo uc (fun _ m ↦ (up m).1) (fun _ m ↦ (up m).2) ⟨y, iu ⟨ys, yb⟩, e⟩
  exact eq.eventuallyEq_of_mem (uo.mem_nhds (iu ⟨zs, zr⟩))

/-- A particular `g` that continues `f` near `x` -/
def Base.g (b : Base p s f) (x : closure s) : E → α :=
  choose (b.ball x)

/-- The radius on which `g` is valid around `x` -/
def Base.r (b : Base p s f) (x : closure s) : ℝ :=
  choose (choose_spec (b.ball x))

/-- The radius is positive -/
lemma Base.rp (b : Base p s f) (x : closure s) : 0 < b.r x :=
  (choose_spec (choose_spec (b.ball x))).1

/-- `g` is valid on `ball x r`-/
lemma Base.gp (b : Base p s f) (x : closure s) (m : z ∈ Metric.ball (x : E) (b.r x)) :
    p (b.g x) z :=
  (choose_spec (choose_spec (b.ball x))).2.1 _ m

/-- `g` matches `f` where they are both defined -/
lemma Base.gf (b : Base p s f) (x : closure s) :
    b.g x =ᶠ[𝓝ˢ (s ∩ Metric.ball (x : E) (b.r x))] f :=
  (choose_spec (choose_spec (b.ball x))).2.2

/-- There exists a finite subcover of the `g` balls -/
lemma Base.exists_cover (b : Base p s f) :
    ∃ c : Finset (closure s), closure s ⊆ ⋃ (x) (_ : x ∈ c), Metric.ball (x : E) (b.r x) := by
  refine b.compact.elim_finite_subcover (fun x : closure s ↦ Metric.ball (x : E) (b.r x))
    (fun _ ↦ isOpen_ball) ?_
  intro x m; exact mem_iUnion_of_mem ⟨x, m⟩ (mem_ball_self (b.rp ⟨x, m⟩))

/-- Choose a finite subcover of the `g` balls -/
def Base.c (b : Base p s f) : Finset (closure s) :=
  choose b.exists_cover

/-- The union of our chosen finite set of `g` balls -/
def Base.t (b : Base p s f) : Set E :=
  ⋃ (x) (_ : x ∈ b.c), Metric.ball (x : E) (b.r x)

/-- Map a point in the union of our ball cover to one ball that contains it -/
def Base.y (b : Base p s f) (m : z ∈ b.t) : closure s :=
  choose (mem_iUnion.mp m)

lemma Base.yt (b : Base p s f) (m : z ∈ b.t) : z ∈ Metric.ball (b.y m : E) (b.r (b.y m)) := by
  simp only [Base.t, Base.y, mem_iUnion₂, mem_iUnion] at m ⊢; exact choose_spec (choose_spec m)

lemma Base.ot (b : Base p s f) : IsOpen b.t :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_ball

theorem Base.cover (b : Base p s f) : closure s ⊆ b.t :=
  choose_spec b.exists_cover

/-- Given two intersecting balls centered in `closure s`, their intersection touches `s` -/
theorem Convex.inter_ball (c : Convex ℝ s) (x0 x1 : closure s) {r0 r1 : ℝ} (r0p : 0 < r0)
    (r1p : 0 < r1) (ne : ∃ z, z ∈ ball (x0 : E) r0 ∩ ball (x1 : E) r1) :
    ∃ w, w ∈ s ∩ ball (x0 : E) r0 ∩ ball (x1 : E) r1 := by
  rcases x0 with ⟨x0, m0⟩; rcases x1 with ⟨x1, m1⟩; simp only [Subtype.coe_mk]
  have x01 : ‖x1 - x0‖ < r0 + r1 := by
    rcases ne with ⟨z, m0, m1⟩; simp only [mem_ball, dist_eq_norm] at m0 m1
    calc ‖x1 - x0‖
      _ = ‖z - x0 - (z - x1)‖ := by abel_nf
      _ ≤ ‖z - x0‖ + ‖z - x1‖ := (norm_sub_le _ _)
      _ < r0 + r1 := add_lt_add m0 m1
  have sub : ∀ (x : E) {a b : ℝ}, 0 < a → 0 < b → (a / (a + b)) • x - x = -((b / (a + b)) • x) := by
    intro x a b ap bp; have rnz := (add_pos ap bp).ne'
    calc (a / (a + b)) • x - x
      _ = (a / (a + b) - (a + b) / (a + b)) • x := by simp only [one_smul, sub_smul, div_self rnz]
      _ = -((b / (a + b)) • x) := by rw [← sub_div, sub_add_cancel', neg_div, neg_smul]
  have le : ∀ {a : ℝ}, 0 < a → a / (r0 + r1) * ‖x1 - x0‖ < a := by
    intro a ap; apply lt_of_lt_of_le (mul_lt_mul_of_pos_left x01 (div_pos ap (add_pos r0p r1p)))
    rw [div_mul_cancel _ (add_pos r0p r1p).ne']
  have e : ∀ᶠ p : E × E in 𝓝 (x0, x1),
      (r1 / (r0 + r1)) • p.1 + (r0 / (r0 + r1)) • p.2 ∈ ball x0 r0 ∩ ball x1 r1 := by
    refine ContinuousAt.eventually_mem ?_ (isOpen_ball.inter isOpen_ball) ?_
    · exact ((continuous_fst.const_smul _).add (continuous_snd.const_smul _)).continuousAt
    · simp only [mem_inter_iff, mem_ball, dist_eq_norm, ← sub_add_eq_add_sub _ x0 _,
        add_sub_assoc _ _ x1]
      nth_rw 1 [add_comm r0 r1]; simp only [sub _ r0p r1p, sub _ r1p r0p]
      simp only [add_comm r1 r0, neg_add_eq_sub, ← sub_eq_add_neg, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_div, abs_of_pos r0p, abs_of_pos r1p, abs_of_pos (add_pos r0p r1p),
        norm_sub_rev (x0 : E) x1]
      use le r0p, le r1p
  have f : ∃ᶠ p : E × E in 𝓝 (x0, x1), p.1 ∈ s ∧ p.2 ∈ s := by
    simp only [nhds_prod_eq]; rw [Prod.frequently (p := fun x ↦ x ∈ s) (q := fun x ↦ x ∈ s)]
    use mem_closure_iff_frequently.mp m0, mem_closure_iff_frequently.mp m1
  rcases(f.and_eventually e).exists with ⟨⟨z0, z1⟩, ⟨m0, m1⟩, m⟩
  refine' ⟨_, ⟨_, m.1⟩, m.2⟩
  apply c m0 m1; bound; bound
  simp only [← add_div, add_comm r1 r0, div_self (add_pos r0p r1p).ne']

/-- Our full continuation `u` throughout `closure s` -/
def Base.u (b : Base p s f) : E → α := fun z ↦
  if m : z ∈ b.t then b.g (b.y m) z else f z

/-- The continuation `u` is equal to each `g` -/
theorem Base.ug (b : Base p s f) (x : closure s) :
    EqOn b.u (b.g x) (b.t ∩ Metric.ball (x : E) (b.r x)) := by
  intro z ⟨zt, m⟩; simp only [Base.u, zt, dif_pos]
  refine b.unique (isOpen_ball.inter isOpen_ball)
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    (fun _ m ↦ b.gp _ (inter_subset_left _ _ m)) (fun _ m ↦ b.gp _ (inter_subset_right _ _ m))
    ?_ ⟨b.yt zt, m⟩
  rcases b.convex.inter_ball (b.y zt) x (b.rp _) (b.rp _) ⟨_, ⟨b.yt zt, m⟩⟩ with ⟨w, m⟩
  exact ⟨w, ⟨m.1.2, m.2⟩, _root_.trans ((b.gf _).self_set _ ⟨m.1.1, m.1.2⟩)
    ((b.gf x).self_set _ ⟨m.1.1, m.2⟩).symm⟩

/-- `u` is equal to our original `f` -/
theorem Base.uf (b : Base p s f) : b.u =ᶠ[𝓝ˢ s] f := by
  simp only [Filter.EventuallyEq, Filter.eventually_iff, mem_nhdsSet_iff_forall]
  intro z m; simp only [← Filter.eventually_iff]
  set x : closure s := ⟨z, subset_closure m⟩
  have zs : z ∈ Metric.ball (x : E) (b.r x) := mem_ball_self (b.rp x)
  have ug := (b.ug x).eventuallyEq_of_mem ((b.ot.inter isOpen_ball).mem_nhds
    ⟨b.cover (subset_closure m), zs⟩)
  exact ug.trans ((b.gf x).filter_mono (nhds_le_nhdsSet ⟨m, zs⟩))

/-- `u` is valid in `𝓝ˢ (closure s)` -/
theorem Base.up (b : Base p s f) : ∀ᶠ z in 𝓝ˢ (closure s), p b.u z := by
  apply Filter.eventually_of_mem (b.ot.mem_nhdsSet.mpr b.cover)
  intro x m; refine' b.congr (b.gp (b.y m) (b.yt m)) _
  exact ((b.ug _).eventuallyEq_of_mem ((b.ot.inter isOpen_ball).mem_nhds ⟨m, b.yt m⟩)).symm

end Continuation
