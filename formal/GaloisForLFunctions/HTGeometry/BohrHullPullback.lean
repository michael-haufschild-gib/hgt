import GaloisForLFunctions.HTGeometry.BohrHullGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The hull is the space of translation limits, and every hull observable is almost periodic

Two structural facts about the Bohr hull.

First, the hull embeds isometrically into the bounded continuous functions on the line: a hull point
`x` is faithfully described by the function `t ↦ ev (x + ι t)`, which for `x = ι s` is the translate
`f (· + s)`.  So distinct hull points are distinguished by evaluations, and the hull really is the
space of uniform translation limits of `f`.

Second, every continuous function on the hull pulls back along `ι` to a Bohr almost-periodic
function on the line: the almost periods of `f` are exactly the times at which `ι` returns close to
the origin of the hull, and the hull metric is translation invariant.  This is the mechanism that
turns the compact group into a source of almost-periodic observables.
-/

open Filter Topology Metric

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : ℝ →ᵇ E}

omit [CompleteSpace E] in
theorem dist_bohrIota (f : ℝ →ᵇ E) (s t : ℝ) :
    dist (bohrIota f s) (bohrIota f t) = dist (BohrLine.of f s) (BohrLine.of f t) :=
  UniformSpace.Completion.dist_eq _ _

omit [CompleteSpace E] in
theorem dense_bohrIota_prod (f : ℝ →ᵇ E) :
    Dense (Set.range (bohrIota f) ×ˢ Set.range (bohrIota f)) := by
  have := (denseRange_bohrIota f).prodMap (denseRange_bohrIota f)
  simpa [DenseRange, Prod.map] using this

omit [CompleteSpace E] in
/-- The hull metric is invariant under translation by the image of the line. -/
theorem dist_add_bohrIota (f : ℝ →ᵇ E) (t : ℝ) (x y : BohrHull f) :
    dist (x + bohrIota f t) (y + bohrIota f t) = dist x y := by
  have h1 : Continuous fun p : BohrHull f × BohrHull f =>
      dist (p.1 + bohrIota f t) (p.2 + bohrIota f t) :=
    continuous_dist.comp ((continuous_fst.add continuous_const).prodMk
      (continuous_snd.add continuous_const))
  have h2 : Continuous fun p : BohrHull f × BohrHull f => dist p.1 p.2 := continuous_dist
  have heq : Set.EqOn (fun p : BohrHull f × BohrHull f =>
      dist (p.1 + bohrIota f t) (p.2 + bohrIota f t))
      (fun p : BohrHull f × BohrHull f => dist p.1 p.2)
      (Set.range (bohrIota f) ×ˢ Set.range (bohrIota f)) := by
    rintro ⟨x, y⟩ ⟨⟨s, rfl⟩, ⟨r, rfl⟩⟩
    simp only
    rw [← bohrIota_add, ← bohrIota_add, dist_bohrIota, dist_bohrIota]
    exact BohrLine.dist_add_right (BohrLine.of f s) (BohrLine.of f r) (BohrLine.of f t)
  exact congrFun (Continuous.ext_on (dense_bohrIota_prod f) h1 h2 heq) (x, y)

theorem norm_bohrEval_le (f : ℝ →ᵇ E) (x : BohrHull f) : ‖bohrEval f x‖ ≤ ‖f‖ := by
  have hcl : IsClosed {z : BohrHull f | ‖bohrEval f z‖ ≤ ‖f‖} :=
    isClosed_le (continuous_bohrEval f).norm continuous_const
  have hsub : Set.range (bohrIota f) ⊆ {z : BohrHull f | ‖bohrEval f z‖ ≤ ‖f‖} := by
    rintro z ⟨t, rfl⟩
    simpa using f.norm_coe_le_norm t
  have := hcl.closure_subset_iff.mpr hsub
  rw [(denseRange_bohrIota f).closure_range] at this
  exact this (Set.mem_univ x)

/-- The evaluation of the hull is `1`-Lipschitz. -/
theorem dist_bohrEval_le (f : ℝ →ᵇ E) (x y : BohrHull f) :
    dist (bohrEval f x) (bohrEval f y) ≤ dist x y := by
  have h1 : Continuous fun p : BohrHull f × BohrHull f =>
      dist (bohrEval f p.1) (bohrEval f p.2) :=
    continuous_dist.comp (((continuous_bohrEval f).comp continuous_fst).prodMk
      ((continuous_bohrEval f).comp continuous_snd))
  have h2 : Continuous fun p : BohrHull f × BohrHull f => dist p.1 p.2 := continuous_dist
  have hcl : IsClosed {p : BohrHull f × BohrHull f |
      dist (bohrEval f p.1) (bohrEval f p.2) ≤ dist p.1 p.2} := isClosed_le h1 h2
  have hsub : (Set.range (bohrIota f) ×ˢ Set.range (bohrIota f)) ⊆
      {p : BohrHull f × BohrHull f | dist (bohrEval f p.1) (bohrEval f p.2) ≤ dist p.1 p.2} := by
    rintro ⟨x, y⟩ ⟨⟨s, rfl⟩, ⟨r, rfl⟩⟩
    have hd := BoundedContinuousFunction.dist_coe_le_dist
      (f := translateBC s f) (g := translateBC r f) 0
    rw [translateBC_apply, translateBC_apply, zero_add, zero_add] at hd
    simpa [dist_bohrIota, BohrLine.dist_eq] using hd
  have := hcl.closure_subset_iff.mpr hsub
  rw [(dense_bohrIota_prod f).closure_eq] at this
  exact this (Set.mem_univ (x, y))

variable (hf : UniformContinuous (fun x => f x))

/-- The bounded continuous function described by a hull point. -/
def bohrHullBC (f : ℝ →ᵇ E) (hf : UniformContinuous (fun x => f x)) (x : BohrHull f) : ℝ →ᵇ E :=
  ⟨⟨fun t => bohrEval f (x + bohrIota f t),
      (continuous_bohrEval f).comp (continuous_const.add (continuous_bohrIota hf))⟩, by
    refine ⟨2 * ‖f‖, fun s t => ?_⟩
    calc dist (bohrEval f (x + bohrIota f s)) (bohrEval f (x + bohrIota f t))
        ≤ ‖bohrEval f (x + bohrIota f s)‖ + ‖bohrEval f (x + bohrIota f t)‖ :=
          dist_le_norm_add_norm _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (norm_bohrEval_le f _) (norm_bohrEval_le f _)
      _ = 2 * ‖f‖ := by ring⟩

@[simp] theorem bohrHullBC_apply (x : BohrHull f) (t : ℝ) :
    bohrHullBC f hf x t = bohrEval f (x + bohrIota f t) := rfl

theorem bohrHullBC_bohrIota (s : ℝ) : bohrHullBC f hf (bohrIota f s) = translateBC s f := by
  ext t
  rw [bohrHullBC_apply, ← bohrIota_add, bohrEval_bohrIota, translateBC_apply, add_comm]

theorem dist_bohrHullBC_le (x y : BohrHull f) :
    dist (bohrHullBC f hf x) (bohrHullBC f hf y) ≤ dist x y := by
  refine (BoundedContinuousFunction.dist_le dist_nonneg).mpr fun t => ?_
  calc dist (bohrHullBC f hf x t) (bohrHullBC f hf y t)
      ≤ dist (x + bohrIota f t) (y + bohrIota f t) := dist_bohrEval_le f _ _
    _ = dist x y := dist_add_bohrIota f t x y

theorem continuous_bohrHullBC : Continuous (bohrHullBC f hf) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
    simpa using dist_bohrHullBC_le hf x y).continuous

/-- **The hull embeds isometrically into the bounded continuous functions.** -/
theorem dist_bohrHullBC (x y : BohrHull f) :
    dist (bohrHullBC f hf x) (bohrHullBC f hf y) = dist x y := by
  have h1 : Continuous fun p : BohrHull f × BohrHull f =>
      dist (bohrHullBC f hf p.1) (bohrHullBC f hf p.2) :=
    continuous_dist.comp (((continuous_bohrHullBC hf).comp continuous_fst).prodMk
      ((continuous_bohrHullBC hf).comp continuous_snd))
  have h2 : Continuous fun p : BohrHull f × BohrHull f => dist p.1 p.2 := continuous_dist
  have heq : Set.EqOn
      (fun p : BohrHull f × BohrHull f => dist (bohrHullBC f hf p.1) (bohrHullBC f hf p.2))
      (fun p : BohrHull f × BohrHull f => dist p.1 p.2)
      (Set.range (bohrIota f) ×ˢ Set.range (bohrIota f)) := by
    rintro ⟨x, y⟩ ⟨⟨s, rfl⟩, ⟨r, rfl⟩⟩
    simp only
    rw [bohrHullBC_bohrIota, bohrHullBC_bohrIota, dist_bohrIota]
    rfl
  exact congrFun (Continuous.ext_on (dense_bohrIota_prod f) h1 h2 heq) (x, y)

include hf in
/-- Distinct hull points are separated by the evaluations along the line. -/
theorem bohrHull_ext {x y : BohrHull f}
    (h : ∀ t : ℝ, bohrEval f (x + bohrIota f t) = bohrEval f (y + bohrIota f t)) : x = y := by
  have hbc : bohrHullBC f hf x = bohrHullBC f hf y := by
    ext t
    exact h t
  have := dist_bohrHullBC hf x y
  rw [hbc, dist_self] at this
  exact dist_eq_zero.mp this.symm

omit [CompleteSpace E] in
/-- **Every continuous observable of the hull pulls back to an almost-periodic function.** -/
theorem isBohrAlmostPeriodic_comp_bohrIota (htb : HasTotallyBoundedOrbit (fun x => f x))
    {F : BohrHull f → ℂ} (hF : Continuous F) :
    HTGeometry.IsBohrAlmostPeriodic (fun t => F (bohrIota f t)) := by
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  have hFu : UniformContinuous F := CompactSpace.uniformContinuous_of_continuous hF
  intro ε hε
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuous_iff.mp hFu (ε := ε) hε
  obtain ⟨L, hL, hdense⟩ :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htb (δ / 2) (by linarith)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun t => ?_⟩
  have hdτ : dist (bohrIota f τ) (0 : BohrHull f) ≤ δ / 2 := by
    have h0 : (0 : BohrHull f) = bohrIota f 0 := (bohrIota_zero f).symm
    rw [h0, dist_bohrIota]
    show dist (translateBC τ f) (translateBC 0 f) ≤ δ / 2
    refine (BoundedContinuousFunction.dist_le (by linarith)).mpr fun x => ?_
    have := hτ x
    rwa [dist_eq_norm, translateBC_apply, translateBC_apply, add_zero]
  have hstep : dist (bohrIota f (t + τ)) (bohrIota f t) ≤ δ / 2 := by
    have h := dist_add_bohrIota f t (bohrIota f τ) 0
    rw [zero_add, ← bohrIota_add, add_comm τ t] at h
    rw [h]
    exact hdτ
  have hlt : dist (bohrIota f (t + τ)) (bohrIota f t) < δ := lt_of_le_of_lt hstep (by linarith)
  have := hδF hlt
  rw [dist_eq_norm] at this
  exact le_of_lt this

end

end GaloisForLFunctions
