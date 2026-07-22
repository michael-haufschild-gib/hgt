import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniDyadicUniversalityLaw
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw
import GaloisForLFunctions.RHTower.XiReciprocalSquareSourceUniversalityLaw

/-!
# Xi Cassini--theta reciprocal-source universality

The genuine inward theta trace at the Euler-safe Cassini center supplies a common zero fibre for
the squared-seam Jensen/dyadic phase and the reciprocal-square operator/Cauchy-source phase.  This
module packages that theorem-generated closure, including direct reflection-energy and fixed-source
welds proved below the separate RH equivalences.
-/

open Complex

namespace RHTower

noncomputable section

/-- Simultaneous Cassini source, dyadic/Hankel, intrinsic jet, reflection-energy, operator, and
continued-Cauchy realization of genuine inward theta-boundary saturation. -/
def XiCassiniThetaReciprocalSourceUniversalCertificate : Prop :=
  XiSquaredSeamCassiniDyadicUniversalCertificate ∧
  XiSquaredSeamCassiniGlobalSourceCertificate ∧
  4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal +
      (iteratedDeriv 63 (logDeriv xiSquaredSeamCassiniSource) 0).re /
        ((63 : ℕ).factorial : ℝ) = 0 ∧
  xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy = 0 ∧
  xiThermalSquareReflectionDefectEnergy = 0 ∧
  HilbertSchmidt.hsNormSq
      (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
        HilbertSchmidt.hsAdjoint
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1)) = 0 ∧
  XiReciprocalSquareGaussianRatOrientationDefectsVanish ∧
  XiReciprocalSquareGaussianRatCauchyQuadraticReal ∧
  XiReciprocalSquareFixedCauchyOrientationDefectZero ∧
  XiReciprocalSquareSourceUniversalCertificate

/-- **Xi Cassini--theta reciprocal-source universality law.** Saturation of the genuine inward
theta boundary is equivalent to simultaneous realization of the complete squared-seam
Cassini--dyadic certificate, its intrinsic Jensen/jet zero residual, both reflection energies,
the reciprocal-square Hilbert--Schmidt zero defect, countable and fixed Cauchy source charts, and
the full reciprocal-square source certificate. -/
theorem thetaCuspCassiniInwardBoundarySaturated_iff_reciprocalSourceUniversalCertificate :
    ThetaCuspCassiniInwardBoundarySaturated ↔
      XiCassiniThetaReciprocalSourceUniversalCertificate := by
  constructor
  · intro htheta
    have hRH : RiemannHypothesis :=
      thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis.1 htheta
    have hdom : XiSquaredSeamPowerSixtyFourSourceDominated :=
      xiSquaredSeamPowerSixtyFourSourceDominated_iff_riemannHypothesis.2 hRH
    have hreciprocal : XiReciprocalSquareSourceUniversalCertificate :=
      xiReciprocalSquareOperator_isSelfAdjoint_iff_sourceUniversalCertificate.1
        (xiReciprocalSquareOperator_isSelfAdjoint_iff_riemannHypothesis.2 hRH)
    exact ⟨
      xiSquaredSeamPowerSixtyFourSourceDominated_iff_cassiniDyadicUniversalCertificate.1 hdom,
      xiSquaredSeamCassiniGlobalSourceCertificate_proof,
      intrinsicCassiniJetResidual_eq_zero_iff_riemannHypothesis.2 hRH,
      thetaCuspCassiniInwardBoundarySaturated_iff_reflectionDefect_zero.1 htheta,
      thetaCuspCassiniInwardBoundarySaturated_iff_thermalReflectionDefect_zero.1 htheta,
      thetaCuspCassiniInwardBoundarySaturated_iff_reciprocalSquareKernel_adjointDefect_zero.1
        htheta,
      thetaCuspCassiniInwardBoundarySaturated_iff_gaussianRatOrientationDefectsVanish.1 htheta,
      thetaCuspCassiniInwardBoundarySaturated_iff_gaussianRatCauchyQuadraticReal.1 htheta,
      thetaCuspCassiniInwardBoundarySaturated_iff_fixedCauchyOrientationDefectZero.1 htheta,
      hreciprocal⟩
  · rintro ⟨_hdyadic, _hglobal, _hintrinsic, _hreflection, _hthermal, _hkernel,
      _hgaussian, _hquadratic, hfixed, _hreciprocal⟩
    exact thetaCuspCassiniInwardBoundarySaturated_iff_fixedCauchyOrientationDefectZero.2 hfixed

/-- Simultaneous squared-seam and reciprocal-source failure packets, together with failure of the
single fixed off-axis Cauchy orientation test. -/
def XiCassiniThetaReciprocalSourceFailureUniversalCertificate : Prop :=
  XiSquaredSeamCassiniDyadicFailureUniversalCertificate ∧
  XiReciprocalSquareSourceFailureUniversalCertificate ∧
  (¬XiReciprocalSquareFixedCauchyOrientationDefectZero) ∧
  0 < xiReciprocalSquareContinuedCauchyOrientationDefect
    xiReciprocalSquareFixedCauchyPole

/-- **Complementary Cassini--theta reciprocal-source failure law.** Failure of genuine inward
theta saturation is equivalent to simultaneous squared-seam dyadic/Hankel failure,
reciprocal-square operator/source failure, and failure of one concrete off-axis Cauchy test. -/
theorem not_thetaCuspCassiniInwardBoundarySaturated_iff_reciprocalSourceFailureCertificate :
    ¬ThetaCuspCassiniInwardBoundarySaturated ↔
      XiCassiniThetaReciprocalSourceFailureUniversalCertificate := by
  constructor
  · intro hnotTheta
    have hnotRH : ¬RiemannHypothesis := by
      intro hRH
      exact hnotTheta
        (thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis.2 hRH)
    refine ⟨
      not_riemannHypothesis_iff_squaredSeamCassiniDyadicFailureUniversalCertificate.1 hnotRH,
      not_riemannHypothesis_iff_reciprocalSquareSourceFailureUniversalCertificate.1 hnotRH,
      ?_,
      xiReciprocalSquareFixedCauchyOrientationDefect_pos_iff_not_riemannHypothesis.2 hnotRH⟩
    intro hfixed
    exact hnotRH
      (xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.1 hfixed)
  · intro hfailure htheta
    have hRH : RiemannHypothesis :=
      thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis.1 htheta
    exact
      (not_riemannHypothesis_iff_squaredSeamCassiniDyadicFailureUniversalCertificate.2
        hfailure.1) hRH

end

end RHTower
