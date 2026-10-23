import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureLikelihoodTax
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureLikelihoodSlopeTax
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCompletedProductFiberOddPtolemyNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCompensationNeutralAnchor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterCompensationTransitionSlack

set_option autoImplicit false

/-!
# Theta-cusp premises discharged at a corpus witness

Three consumers hold at every point satisfying a premise that the corpus realises at some point:

* the first-fiber rise `A₁(0) < A₁(t)` (`exists_thetaCuspCompletedProductFiberAmplitude_one_rise`)
  makes the cofinal convexity and slope-square taxes at zero positive;
* a positive zero of the center compensation source
  (`exists_thetaCuspCenterCompensationFlux_transition_pos`) is a transverse crossing.
-/

namespace RHTower

/-- The cofinal likelihood convexity tax at zero is positive at some positive time. -/
theorem exists_thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero_pos :
    ∃ t : ℝ, 0 < t ∧ 0 < thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero t := by
  obtain ⟨t, ht, hrise⟩ := exists_thetaCuspCompletedProductFiberAmplitude_one_rise
  exact ⟨t, ht, thetaCuspCompletedProductFiberCofinalLikelihoodConvexityTaxAtZero_pos ht hrise⟩

/-- The cofinal likelihood slope-square tax at zero is positive at some positive time. -/
theorem exists_thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero_pos :
    ∃ t : ℝ, 0 < t ∧
      0 < thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero t := by
  obtain ⟨t, ht, hrise⟩ := exists_thetaCuspCompletedProductFiberAmplitude_one_rise
  exact ⟨t, ht, thetaCuspCompletedProductFiberCofinalLikelihoodSlopeSquareTaxAtZero_pos ht hrise⟩

/-- The center compensation source has a positive transverse zero. -/
theorem exists_thetaCuspCenterCompensationSource_transverse_zero :
    ∃ x : ℝ, 0 < x ∧ thetaCuspCenterCompensationSource x = 0 ∧
      x * deriv thetaCuspCenterCompensationSource x < -3 * thetaCuspFullSource x ^ (2 : ℕ) := by
  obtain ⟨x, hx, hz, -⟩ := exists_thetaCuspCenterCompensationFlux_transition_pos
  exact ⟨x, hx, hz, thetaCuspCenterCompensationSource_zero_transverse hx hz⟩

end RHTower
