import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaStageGreenBoundaryCofinalMixedInertia
import GaloisForLFunctions.HTGeometry.HermitianDefiniteSubspaceRankBound

/-!
# The pinned boundary form is exactly one hyperbolic plane, on the limit and on every late stage

The universal pinned-Volterra boundary form on `L²(0,1)` is self-adjoint of rank two and carries
the quadratic values `+1/6` and `-1/6`.  Hence its positive index and its negative index are both
exactly one: it is one hyperbolic plane, not merely "neither semidefinite".

The actual theta-stage Green boundaries converge to it in operator norm.  At margin `1/13` — which
is exactly the ratio `(1/12)/(13/12)` of the corpus's late-stage quadratic margin to the squared
norm of the fixed source witnesses — every sufficiently late stage therefore has exactly one
`1/13`-positive square and exactly one `1/13`-negative square.
-/

open Complex Filter GaloisForLFunctions.HTGeometry

namespace RHTower.HedenmalmThetaSource

open RHTower

noncomputable section

/-- The pinned boundary form is self-adjoint. -/
theorem pinnedBoundaryCLM_isSelfAdjoint : IsSelfAdjoint pinnedBoundaryCLM :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr pinnedBoundaryCLM_adjoint_eq

/-- The affine boundary plane `span {1, t}` is finite-dimensional. -/
theorem finiteDimensional_pinnedAffineSubspace : FiniteDimensional ℂ pinnedAffineSubspace := by
  unfold pinnedAffineSubspace
  exact FiniteDimensional.span_of_finite ℂ (Set.toFinite _)

/-- The range of the pinned boundary form is finite-dimensional. -/
theorem finiteDimensional_range_pinnedBoundaryCLM :
    FiniteDimensional ℂ (LinearMap.range pinnedBoundaryCLM.toLinearMap) := by
  rw [range_pinnedBoundaryCLM_eq_affineSubspace]
  exact finiteDimensional_pinnedAffineSubspace

/-- The positive witness has quadratic value `1/6`. -/
theorem reQuad_pinnedBoundaryCLM_pinnedPositiveMode :
    reQuad pinnedBoundaryCLM pinnedPositiveMode = 1 / 6 := by
  unfold reQuad
  rw [inner_pinnedBoundaryCLM_pinnedPositiveMode]
  norm_num

/-- The negative witness has quadratic value `-1/6`. -/
theorem reQuad_pinnedBoundaryCLM_pinnedNegativeMode :
    reQuad pinnedBoundaryCLM pinnedNegativeMode = -1 / 6 := by
  unfold reQuad
  rw [inner_pinnedBoundaryCLM_pinnedNegativeMode]
  norm_num

theorem reQuad_pinnedBoundaryCLM_pinnedPositiveMode_pos :
    0 < reQuad pinnedBoundaryCLM pinnedPositiveMode := by
  rw [reQuad_pinnedBoundaryCLM_pinnedPositiveMode]
  norm_num

theorem reQuad_pinnedBoundaryCLM_pinnedNegativeMode_neg :
    reQuad pinnedBoundaryCLM pinnedNegativeMode < 0 := by
  rw [reQuad_pinnedBoundaryCLM_pinnedNegativeMode]
  norm_num

/-- **The pinned boundary form is exactly one hyperbolic plane.**  Every strictly positive subspace
has dimension at most one and a strictly positive line exists; every strictly negative subspace has
dimension at most one and a strictly negative line exists. -/
theorem pinnedBoundaryCLM_exact_inertia :
    (∀ V : Submodule ℂ H, StrictPositiveOn pinnedBoundaryCLM V →
        FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ 1) ∧
    (∃ V : Submodule ℂ H, Module.finrank ℂ V = 1 ∧ StrictPositiveOn pinnedBoundaryCLM V) ∧
    (∀ W : Submodule ℂ H, StrictNegativeOn pinnedBoundaryCLM W →
        FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ 1) ∧
    (∃ W : Submodule ℂ H, Module.finrank ℂ W = 1 ∧ StrictNegativeOn pinnedBoundaryCLM W) := by
  haveI := finiteDimensional_range_pinnedBoundaryCLM
  exact rankTwo_mixed_exact_inertia pinnedBoundaryCLM_isSelfAdjoint
    finrank_range_pinnedBoundaryCLM reQuad_pinnedBoundaryCLM_pinnedPositiveMode_pos
    reQuad_pinnedBoundaryCLM_pinnedNegativeMode_neg

/-- Operator-norm convergence to the pinned form, in `∀ᶠ` form. -/
theorem eventually_norm_thetaSourceSignedStageGreenBoundary_sub_pinned_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ‖thetaSourceSignedStageGreenBoundary k - pinnedBoundaryCLM‖ < ε := by
  have h := thetaSourceSignedStageGreenBoundary_tendsto_pinned
  rw [Metric.tendsto_atTop] at h
  obtain ⟨K, hK⟩ := h ε hε
  refine Filter.eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
  rw [← dist_eq_norm]
  exact hK k hk

/-- **Every late theta stage is exactly one hyperbolic plane at margin `1/13`.**  Eventually in the
stage index, every `1/13`-positive subspace of the actual Green boundary has dimension at most one
and a `1/13`-positive line exists, and the same holds on the negative side. -/
theorem eventually_thetaSourceSignedStageGreenBoundary_exact_margin_inertia :
    ∀ᶠ k in atTop,
      (∀ V : Submodule ℂ H,
          MarginPositiveOn (thetaSourceSignedStageGreenBoundary k) (1 / 13) V →
            FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ 1) ∧
      (∃ V : Submodule ℂ H, Module.finrank ℂ V = 1 ∧
          MarginPositiveOn (thetaSourceSignedStageGreenBoundary k) (1 / 13) V) ∧
      (∀ W : Submodule ℂ H,
          MarginNegativeOn (thetaSourceSignedStageGreenBoundary k) (1 / 13) W →
            FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ 1) ∧
      (∃ W : Submodule ℂ H, Module.finrank ℂ W = 1 ∧
          MarginNegativeOn (thetaSourceSignedStageGreenBoundary k) (1 / 13) W) := by
  filter_upwards [eventually_norm_thetaSourceSignedStageGreenBoundary_sub_pinned_lt
      (ε := (1 : ℝ) / 13) (by norm_num),
    eventually_thetaSourceSignedStageGreenBoundary_fixed_mixedInertia] with k hnorm hmix
  haveI := finiteDimensional_range_pinnedBoundaryCLM
  have hcalc : ((1 : ℝ) / 13) * ((13 : ℝ) / 12) = 1 / 12 := by norm_num
  have hp : ((1 : ℝ) / 13) * ‖pinnedPositiveMode‖ ^ (2 : ℕ) <
      reQuad (thetaSourceSignedStageGreenBoundary k) pinnedPositiveMode := by
    rw [norm_pinnedPositiveMode_sq, hcalc]
    exact hmix.1
  have hm : reQuad (thetaSourceSignedStageGreenBoundary k) pinnedNegativeMode <
      -(((1 : ℝ) / 13) * ‖pinnedNegativeMode‖ ^ (2 : ℕ)) := by
    rw [norm_pinnedNegativeMode_sq, hcalc]
    have h2 := hmix.2
    unfold reQuad
    linarith
  exact approximant_exact_margin_inertia pinnedBoundaryCLM_isSelfAdjoint
    finrank_range_pinnedBoundaryCLM reQuad_pinnedBoundaryCLM_pinnedPositiveMode_pos
    reQuad_pinnedBoundaryCLM_pinnedNegativeMode_neg hnorm hp hm

end

end RHTower.HedenmalmThetaSource
