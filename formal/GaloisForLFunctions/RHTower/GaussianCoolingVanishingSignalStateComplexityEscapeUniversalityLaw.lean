import GaloisForLFunctions.RHTower.GaussianWindowHankelRecession
import GaloisForLFunctions.HTGeometry.FiniteStateSpaceHankelRank

/-!
# Gaussian cooling: vanishing signal with escaping state complexity

For every bounded continuous density positive at the cooling centre, all fixed Gaussian-windowed
moment coordinates vanish as the cooling strength tends to infinity.  Nevertheless, every fixed
finite hidden-state dimension is eventually impossible: the corresponding Hankel block is positive
definite, whereas a fixed-dimensional local state-space closure forces that determinant to vanish.

This is a singular realization law.  The family converges pointwise to the zero signal while its
required linear state dimension escapes every fixed bound.
-/

noncomputable section

open Filter Topology

namespace RHTower

/-- Every fixed Gaussian-windowed moment coordinate vanishes under strong cooling. -/
theorem tendsto_gaussianWindowWeightedMoment_atTop_zero
    (J : ℝ → ℝ) (hJc : Continuous J) {C : ℝ} (hJb : ∀ x, |J x| ≤ C) (m : ℕ) :
    Tendsto
      (fun tau : ℝ => weightedMoment (gaussianWindowMeasure tau) J m)
      atTop (𝓝 0) := by
  have hscale :
      Tendsto (fun tau : ℝ => (Real.sqrt tau)⁻¹ ^ (m + 1)) atTop (𝓝 0) := by
    have hinv :
        Tendsto (fun tau : ℝ => (Real.sqrt tau)⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_id).inv_tendsto_atTop
    simpa using hinv.pow (m + 1)
  have hcooled :
      Tendsto (cooledMoment J · m) atTop
        (𝓝 ((∫ y, y ^ m * Real.exp (-y ^ (2 : ℕ))) * J 0)) := by
    simpa [cooledMoment] using tendsto_gaussianCooledMoment J hJc hJb m
  have hproduct :
      Tendsto
        (fun tau : ℝ => (Real.sqrt tau)⁻¹ ^ (m + 1) * cooledMoment J tau m)
        atTop (𝓝 0) := by
    simpa using hscale.mul hcooled
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
  exact (weightedMoment_eq_cooled htau J m).symm

/-- Every fixed linear hidden-state dimension is eventually excluded by Gaussian cooling. -/
theorem eventually_gaussianWindowWeightedMoment_not_fixedStateSpaceDimensionLocalClosure
    {J : ℝ → ℝ} (hJc : Continuous J) {C : ℝ} (hJb : ∀ x, |J x| ≤ C)
    (hJ0 : 0 < J 0) (d : ℕ) :
    ∀ᶠ tau in atTop,
      ¬ HTGeometry.FixedStateSpaceDimensionLocalClosure d
        (weightedMoment (gaussianWindowMeasure tau) J) := by
  filter_upwards [
    gaussianWindow_momentHankelMatrix_posDef_eventually hJc hJb hJ0 (d + 1)
  ] with tau hpd
  exact HTGeometry.not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
    (ne_of_gt hpd.det_pos)

/-- **Gaussian cooling vanishing-signal/state-complexity escape universality law.**
Every coordinate tends to zero, yet every prescribed finite hidden-state dimension is excluded
cofinally along the same cooling parameter. -/
theorem gaussianCooling_vanishingSignal_stateComplexityEscapeUniversality
    {J : ℝ → ℝ} (hJc : Continuous J) {C : ℝ} (hJb : ∀ x, |J x| ≤ C)
    (hJ0 : 0 < J 0) :
    (∀ m : ℕ,
      Tendsto
        (fun tau : ℝ => weightedMoment (gaussianWindowMeasure tau) J m)
        atTop (𝓝 0)) ∧
    (∀ d : ℕ, ∀ᶠ tau in atTop,
      ¬ HTGeometry.FixedStateSpaceDimensionLocalClosure d
        (weightedMoment (gaussianWindowMeasure tau) J)) := by
  exact ⟨fun m => tendsto_gaussianWindowWeightedMoment_atTop_zero J hJc hJb m,
    fun d =>
      eventually_gaussianWindowWeightedMoment_not_fixedStateSpaceDimensionLocalClosure
        hJc hJb hJ0 d⟩

end RHTower
