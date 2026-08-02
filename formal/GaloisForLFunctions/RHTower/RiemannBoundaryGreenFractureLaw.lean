import GaloisForLFunctions.RHTower.RiemannDerivedPolarizationLaw
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw

/-!
# Riemann boundary Green-fracture law

The corpus previously expressed the same obstruction in several charts:

* source-inverse versus analytic-adjoint nearby poles;
* signed source Cayley escape;
* reflected prime-tail entropy;
* finite-Rees versus all-orders-flat valuation sectors;
* the Frobenius--Hodge commutator;
* Wold--Poisson, Sonin--Calkin, and four-unit Ward regularity.

This module proves that these are not merely equivalent zero tests.  Their
local coefficients agree exactly, including sign and normalization.  The
single signed fracture is twice centered horizontal displacement.  It is
the source escape rate, minus reflected entropy, minus weight-one curvature,
and the exact multiplier of the Hodge commutator.

Consequently the remaining source problem is an adjunction problem for one
secondary Green transport: it must make source inverse and analytic adjoint
coincide without erasing the signed first-order coefficient.
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The nearby-pole duality--adjunction fracture is exactly the signed
source-horizon Cayley escape rate. -/
theorem xiNearbyPoleDualityAdjunctionFracture_eq_sourceCayleyRate
    (rho : ℂ) :
    xiNearbyPoleDualityAdjunctionFracture rho =
      (sourceCayleyTransverseRate 1 rho : ℂ) := by
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  apply Complex.ext
  · simp [sourceCayleyTransverseRate, sub_re]
    ring
  · simp

/-- The same fracture is minus reflected source entropy. -/
theorem xiNearbyPoleDualityAdjunctionFracture_eq_neg_reflectedSourceEntropy
    (rho : ℂ) :
    xiNearbyPoleDualityAdjunctionFracture rho =
      -(riemannReflectedSourceEntropy rho : ℂ) := by
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_sourceCayleyRate,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  push_cast
  ring

/-- The same fracture is minus weight-one purity curvature. -/
theorem xiNearbyPoleDualityAdjunctionFracture_eq_neg_weightOnePurityCurvature
    (rho : ℂ) :
    xiNearbyPoleDualityAdjunctionFracture rho =
      -weightOnePurityCurvature rho := by
  rw [weightOnePurityCurvature_eq_reflectedSourceEntropy,
    xiNearbyPoleDualityAdjunctionFracture_eq_neg_reflectedSourceEntropy]

/--
**Orbitwise fracture law.** The Frobenius--Hodge commutator is multiplication
by the source-inverse/analytic-adjoint nearby-pole fracture.
-/
theorem deningerArithmeticOrientedHodge_commutator_apply_eq_boundaryFracture
    (a : DeningerArithmeticGradedH1)
    (q : XiZeroCopy) :
    (deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedHodge.sigma a) -
        deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedTheta a)) q =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) *
        deningerArithmeticGradedOrientedHodge.sigma a q := by
  rw [deningerArithmeticOrientedHodge_commutator_apply_eq_purityCurvature,
    xiNearbyPoleDualityAdjunctionFracture_eq_neg_weightOnePurityCurvature]

/-- In the critical strip, the positive fracture sector is exactly the
all-orders-flat reflected prime-valuation Rees sector. -/
theorem xiNearbyPoleDualityAdjunctionFracture_selects_primeValuationReesType
    (s : ℂ)
    (hstrip : 0 < s.re ∧ s.re < 1) :
    ReesAllOrdersFlat Filter.atTop
        GaloisForLFunctions.primeWoldBoundaryVolumeBelow
        (primeValuationSquaredHellingerBelow (s.re - 1 / 2)) ↔
      0 < (xiNearbyPoleDualityAdjunctionFracture s).re := by
  rw [weightOnePurityCurvature_selects_primeValuationReesType s hstrip,
    xiNearbyPoleDualityAdjunctionFracture_eq_neg_weightOnePurityCurvature]
  simp

/-- Global boundary-character adjunction is exactly weight-one conservation
of the derived divisor metric. -/
theorem xiBoundaryCharacterNeutral_iff_derivedHodgeMetric_weightOne :
    XiBoundaryCharacterNeutral ↔
      ∀ a b : DeningerArithmeticGradedH1,
        deningerArithmeticDerivedHodgeMetric
              (deningerArithmeticGradedTheta a) b +
            deningerArithmeticDerivedHodgeMetric a
              (deningerArithmeticGradedTheta b) =
          deningerArithmeticDerivedHodgeMetric a b := by
  rw [xiBoundaryCharacterNeutral_iff_riemannHypothesis,
    deningerArithmeticDerivedHodgeMetric_weightOne_iff_riemannHypothesis]

/--
The Wold--Poisson, Sonin--Calkin, and four-unit Ward phases are collectively
regular exactly when the same derived Hodge metric conserves weight one.
-/
theorem regularBoundaryConsumers_iff_derivedHodgeMetric_weightOne :
    (XiWoldPoissonQuadrantRegular ∧
        XiPrimeSeamAllScaleCalkinCertificate ∧
        ContinuedXiWardEulerEdgeBoundaryGramLaw) ↔
      ∀ a b : DeningerArithmeticGradedH1,
        deningerArithmeticDerivedHodgeMetric
              (deningerArithmeticGradedTheta a) b +
            deningerArithmeticDerivedHodgeMetric a
              (deningerArithmeticGradedTheta b) =
          deningerArithmeticDerivedHodgeMetric a b := by
  rw [← xiBoundaryCharacterNeutral_iff_regularBoundaryConsumers,
    xiBoundaryCharacterNeutral_iff_derivedHodgeMetric_weightOne]

end

end RHTower
