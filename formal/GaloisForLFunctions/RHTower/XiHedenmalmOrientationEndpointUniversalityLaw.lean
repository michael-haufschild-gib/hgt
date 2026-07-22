import GaloisForLFunctions.RHTower.HedenmalmGaussianHankelApertureWidthSpectrum
import GaloisForLFunctions.RHTower.HedenmalmOrientationVerticalMeshRH
import GaloisForLFunctions.RHTower.XiHedenmalmMomentOrientationBoundary
import GaloisForLFunctions.RHTower.XiHedenmalmNumericalSectorCollision

/-!
# Xi Hedenmalm orientation endpoint universality

The zero-width endpoint of the Gaussian Hedenmalm spectrum, the canonical orientation
multiplier, the reconstructed moment Bezoutian, the rank-one Weil gate, and the reciprocal
numerical sector all detect the same phase.  This module packages their parameter-uniform common
closure and the synchronized failure phase.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Simultaneous realization of the RH endpoint in every currently formalized Hedenmalm
Gaussian, Krein, Fourier, orientation, moment, Cauchy, and multiplicity-aware numerical chart. -/
def XiHedenmalmOrientationEndpointUniversalCertificate : Prop :=
  (∀ tau : ℝ, 0 < tau → HedenmalmGaussianHankelCone tau) ∧
  (∀ tau : ℝ, 0 < tau → HedenmalmGaussianHankelTailCone tau 0) ∧
  ThetaXiHankelOrbitNonnegative ∧
  ThetaCuspCenterMixedFourierNonnegative ∧
  (∀ a : ℝ, 0 < a → XiCanonicalOrientationUpperSingularityCeiling a) ∧
  (∀ a : ℝ, 0 < a →
    AnalyticOnNhd ℂ (xiCanonicalHorizontalOrientationMultiplier a)
      {b : ℂ | a < b.im}) ∧
  (∀ a : ℝ, 0 < a →
    XiCanonicalOrientationUpperVerticalMeshLocallyBoundedBelow a) ∧
  XiHedenmalmUpperHermitianDiagonalNonnegative ∧
  XiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative ∧
  ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
  XiWeilUpperOneCauchyNonnegative ∧
  XiRightHalfLocalJordanNormal ∧
  XiThetaReciprocalNumericalUpperSector

/-- **Hedenmalm orientation endpoint universality law.**  RH is exactly the simultaneous,
parameter-uniform positive phase in all thirteen Hedenmalm endpoint charts. -/
theorem riemannHypothesis_iff_hendenmalmOrientationEndpointUniversalCertificate :
    RiemannHypothesis ↔ XiHedenmalmOrientationEndpointUniversalCertificate := by
  constructor
  · intro hRH
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro tau htau
      exact (hedenmalmGaussianHankelCone_iff_riemannHypothesis htau).2 hRH
    · intro tau htau
      exact (hedenmalmGaussianHankelTailCone_zero_iff_riemannHypothesis htau).2 hRH
    · exact thetaXiHankelOrbitNonnegative_iff_riemannHypothesis.2 hRH
    · exact thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis.2 hRH
    · intro a ha
      exact (orientationUpperSingularityCeiling_iff_riemannHypothesis ha).2 hRH
    · intro a ha
      exact (canonicalOrientation_analyticOnNhd_upperHalfPlane_iff_riemannHypothesis ha).2 hRH
    · intro a ha
      exact (orientationUpperVerticalMeshLocallyBoundedBelow_iff_riemannHypothesis ha).2 hRH
    · exact xiHedenmalmUpperHermitianDiagonalNonnegative_iff_riemannHypothesis.2 hRH
    · exact xiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative_iff_riemannHypothesis.2 hRH
    · exact continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis.2 hRH
    · exact xiWeilUpperOneCauchyNonnegative_iff_riemannHypothesis.2 hRH
    · exact riemannHypothesis_iff_rightHalfLocalJordanNormal_and_numericalUpperSector.1 hRH |>.1
    · exact riemannHypothesis_iff_rightHalfLocalJordanNormal_and_numericalUpperSector.1 hRH |>.2
  · intro hcertificate
    exact (hedenmalmGaussianHankelCone_iff_riemannHypothesis
      (by norm_num : (0 : ℝ) < 1)).1
      (hcertificate.1 1 (by norm_num))

/-- Under failure of RH every exact analytic/sign endpoint fails, while the multiplicity-aware
numerical factorization fails in at least one of its two complementary factors. -/
def XiHedenmalmOrientationEndpointFailureUniversalCertificate : Prop :=
  (∀ tau : ℝ, 0 < tau → ¬ HedenmalmGaussianHankelCone tau) ∧
  (∀ tau : ℝ, 0 < tau → ¬ HedenmalmGaussianHankelTailCone tau 0) ∧
  ¬ ThetaXiHankelOrbitNonnegative ∧
  ¬ ThetaCuspCenterMixedFourierNonnegative ∧
  (∀ a : ℝ, 0 < a → ¬ XiCanonicalOrientationUpperSingularityCeiling a) ∧
  (∀ a : ℝ, 0 < a →
    ¬ AnalyticOnNhd ℂ (xiCanonicalHorizontalOrientationMultiplier a)
      {b : ℂ | a < b.im}) ∧
  (∀ a : ℝ, 0 < a →
    ¬ XiCanonicalOrientationUpperVerticalMeshLocallyBoundedBelow a) ∧
  ¬ XiHedenmalmUpperHermitianDiagonalNonnegative ∧
  ¬ XiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative ∧
  ¬ ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
  ¬ XiWeilUpperOneCauchyNonnegative ∧
  (¬ XiRightHalfLocalJordanNormal ∨
    ¬ XiThetaReciprocalNumericalUpperSector)

/-- **Synchronized Hedenmalm failure law.**  Failure of RH is not confined to one presentation:
it forces failure in every exact Hedenmalm endpoint chart. -/
theorem not_riemannHypothesis_iff_hendenmalmOrientationEndpointFailureUniversalCertificate :
    ¬ RiemannHypothesis ↔
      XiHedenmalmOrientationEndpointFailureUniversalCertificate := by
  constructor
  · intro hnotRH
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro tau htau hcone
      exact hnotRH ((hedenmalmGaussianHankelCone_iff_riemannHypothesis htau).1 hcone)
    · intro tau htau hcone
      exact hnotRH
        ((hedenmalmGaussianHankelTailCone_zero_iff_riemannHypothesis htau).1 hcone)
    · intro horbit
      exact hnotRH (thetaXiHankelOrbitNonnegative_iff_riemannHypothesis.1 horbit)
    · intro hfourier
      exact hnotRH
        (thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis.1 hfourier)
    · intro a ha hceiling
      exact hnotRH
        ((orientationUpperSingularityCeiling_iff_riemannHypothesis ha).1 hceiling)
    · intro a ha hanalytic
      exact hnotRH
        ((canonicalOrientation_analyticOnNhd_upperHalfPlane_iff_riemannHypothesis ha).1
          hanalytic)
    · intro a ha hmesh
      exact hnotRH
        ((orientationUpperVerticalMeshLocallyBoundedBelow_iff_riemannHypothesis ha).1 hmesh)
    · intro hdiag
      exact hnotRH
        (xiHedenmalmUpperHermitianDiagonalNonnegative_iff_riemannHypothesis.1 hdiag)
    · intro hdiag
      exact hnotRH
        (xiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative_iff_riemannHypothesis.1
          hdiag)
    · intro hsource
      exact hnotRH
        (continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis.1 hsource)
    · intro hone
      exact hnotRH (xiWeilUpperOneCauchyNonnegative_iff_riemannHypothesis.1 hone)
    · by_cases hnormal : XiRightHalfLocalJordanNormal
      · exact Or.inr (fun hsector => hnotRH
          (riemannHypothesis_iff_rightHalfLocalJordanNormal_and_numericalUpperSector.2
            ⟨hnormal, hsector⟩))
      · exact Or.inl hnormal
  · intro hfailure hRH
    exact hfailure.1 1 (by norm_num)
      ((hedenmalmGaussianHankelCone_iff_riemannHypothesis
        (by norm_num : (0 : ℝ) < 1)).2 hRH)

/-- The synchronized failure phase is exactly the complement of the positive endpoint phase. -/
theorem not_hendenmalmOrientationEndpointUniversalCertificate_iff_failure :
    ¬ XiHedenmalmOrientationEndpointUniversalCertificate ↔
      XiHedenmalmOrientationEndpointFailureUniversalCertificate := by
  constructor
  · intro hnotCertificate
    apply not_riemannHypothesis_iff_hendenmalmOrientationEndpointFailureUniversalCertificate.1
    intro hRH
    exact hnotCertificate
      (riemannHypothesis_iff_hendenmalmOrientationEndpointUniversalCertificate.1 hRH)
  · intro hfailure hcertificate
    have hnotRH :=
      not_riemannHypothesis_iff_hendenmalmOrientationEndpointFailureUniversalCertificate.2
        hfailure
    exact hnotRH
      (riemannHypothesis_iff_hendenmalmOrientationEndpointUniversalCertificate.2 hcertificate)

end

end RHTower
