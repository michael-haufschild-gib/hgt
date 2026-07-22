import GaloisForLFunctions.RHTower.PrimeArchReciprocalSquareSectorGate
import GaloisForLFunctions.RHTower.XiReciprocalCliffordSquare
import GaloisForLFunctions.RHTower.XiReciprocalSquareCountableCauchySource
import GaloisForLFunctions.RHTower.XiReciprocalSquareFixedCauchySourceReconstruction

/-!
# Xi reciprocal-square source universality

Self-adjointness of the squared reciprocal Xi operator carries exactly the same orientation datum
as the Clifford, continued-Cauchy, countable scalar-defect, centered-spectrum, and prime--Gamma
sector charts.  The complementary theorem packages simultaneous witnesses in the failure chamber.
-/

open Complex

namespace RHTower

noncomputable section

/-- Simultaneous operator, source-core, countable, spectral-coordinate, and sector realization of
reciprocal-square orientation. -/
def XiReciprocalSquareSourceUniversalCertificate : Prop :=
  IsSelfAdjoint xiReciprocalOperator ∧
  XiReciprocalCliffordPolarization ∧
  XiReciprocalSquareContinuedCauchyQuadraticReal ∧
  XiReciprocalSquareOneCauchyQuadraticReal ∧
  XiReciprocalSquareGaussianRatCauchyQuadraticReal ∧
  XiReciprocalSquareGaussianRatOrientationDefectsVanish ∧
  XiReciprocalSquareFixedCauchySourceContrastSaturation ∧
  (∀ ρ : XiDivisorSupport,
    (xiCentralReciprocalSquare (ρ : ℂ)).im = 0) ∧
  XiReciprocalSquareUpperSectorNonnegative ∧
  ContinuedPrimeArchReciprocalSquareUpperSectorNonnegative

/-- **Xi reciprocal-square source universality law.**  Squared self-adjointness is equivalent to
simultaneous realization in nine unsquared, Clifford, Cauchy-source, countable-defect,
centered-spectrum, and prime--Gamma sector charts. -/
theorem xiReciprocalSquareOperator_isSelfAdjoint_iff_sourceUniversalCertificate :
    IsSelfAdjoint xiReciprocalSquareOperator ↔
      XiReciprocalSquareSourceUniversalCertificate := by
  constructor
  · intro hsquare
    have hRH : RiemannHypothesis :=
      xiReciprocalSquareOperator_isSelfAdjoint_iff_riemannHypothesis.1 hsquare
    have henergy : xiHurwitzOrientationEnergy = 0 :=
      riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.1 hRH
    exact ⟨
      xiReciprocalOperator_isSelfAdjoint_iff_rh.2 hRH,
      xiReciprocalCliffordPolarization_iff_riemannHypothesis.2 hRH,
      xiReciprocalSquareContinuedCauchyQuadraticReal_iff_riemannHypothesis.2 hRH,
      xiReciprocalSquareOneCauchyQuadraticReal_iff_riemannHypothesis.2 hRH,
      xiReciprocalSquareGaussianRatCauchyQuadraticReal_iff_riemannHypothesis.2 hRH,
      xiReciprocalSquareGaussianRatOrientationDefectsVanish_iff_riemannHypothesis.2 hRH,
      xiReciprocalSquareFixedCauchySourceContrastSaturation_iff_riemannHypothesis.2 hRH,
      xiHurwitzOrientationEnergy_eq_zero_iff_centralSpectrum_real.1 henergy,
      xiReciprocalSquareUpperSectorNonnegative_iff_riemannHypothesis.2 hRH,
      continuedPrimeArchReciprocalSquareUpperSectorNonnegative_iff_riemannHypothesis.2 hRH⟩
  · intro hcertificate
    exact xiReciprocalSquareOperator_isSelfAdjoint_iff_riemannHypothesis.2
      (xiReciprocalOperator_isSelfAdjoint_iff_rh.1 hcertificate.1)

/-- Simultaneous failure of reciprocal self-adjointness and Clifford polarization, together with
explicit countable, centered-spectrum, target-sector, and source-sector orientation witnesses. -/
def XiReciprocalSquareSourceFailureUniversalCertificate : Prop :=
  (¬ IsSelfAdjoint xiReciprocalOperator) ∧
  (¬ XiReciprocalCliffordPolarization) ∧
  (∃ q : XiGaussianRatContinuedCauchyPoint,
    xiReciprocalSquareGaussianRatOrientationDefect q ≠ 0) ∧
  (¬ XiReciprocalSquareFixedCauchySourceContrastSaturation) ∧
  (∃ ρ : XiDivisorSupport,
    (xiCentralReciprocalSquare (ρ : ℂ)).im ≠ 0) ∧
  (∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ XiC z ≠ 0 ∧
    z.re * (-logDeriv XiC z / z).im < 0) ∧
  (∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧
    riemannZeta (1 / 2 + z * I) ≠ 0 ∧
      z.re * (continuedPrimeArchReciprocalSquareTrace z).im < 0)

/-- **Complementary reciprocal-square source failure law.**  Failure of RH is equivalent to six
simultaneous operator, countable-source, spectral, and sector witnesses. -/
theorem not_riemannHypothesis_iff_reciprocalSquareSourceFailureUniversalCertificate :
    ¬RiemannHypothesis ↔
      XiReciprocalSquareSourceFailureUniversalCertificate := by
  classical
  constructor
  · intro hnotRH
    have hnotOperator : ¬IsSelfAdjoint xiReciprocalOperator := by
      intro hself
      exact hnotRH (xiReciprocalOperator_isSelfAdjoint_iff_rh.1 hself)
    have hnotClifford : ¬XiReciprocalCliffordPolarization := by
      intro hclifford
      exact hnotRH
        (xiReciprocalCliffordPolarization_iff_riemannHypothesis.1 hclifford)
    have hnotDefects :
        ¬XiReciprocalSquareGaussianRatOrientationDefectsVanish := by
      intro hdefects
      exact hnotRH
          (xiReciprocalSquareGaussianRatOrientationDefectsVanish_iff_riemannHypothesis.1
            hdefects)
    have hnotFixedSource :
        ¬XiReciprocalSquareFixedCauchySourceContrastSaturation := by
      intro hsource
      exact hnotRH
        (xiReciprocalSquareFixedCauchySourceContrastSaturation_iff_riemannHypothesis.1
          hsource)
    have hnotTarget : ¬XiReciprocalSquareUpperSectorNonnegative := by
      intro hsector
      exact hnotRH
        (xiReciprocalSquareUpperSectorNonnegative_iff_riemannHypothesis.1 hsector)
    have hnotSource :
        ¬ContinuedPrimeArchReciprocalSquareUpperSectorNonnegative := by
      intro hsector
      exact hnotRH
        (continuedPrimeArchReciprocalSquareUpperSectorNonnegative_iff_riemannHypothesis.1
          hsector)
    rw [XiReciprocalSquareGaussianRatOrientationDefectsVanish] at hnotDefects
    push Not at hnotDefects
    rw [XiReciprocalSquareUpperSectorNonnegative] at hnotTarget
    push Not at hnotTarget
    rw [ContinuedPrimeArchReciprocalSquareUpperSectorNonnegative] at hnotSource
    push Not at hnotSource
    have henergy : 0 < xiHurwitzOrientationEnergy :=
      xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnotRH
    obtain ⟨ρ, hρ⟩ :=
      xiHurwitzOrientationEnergy_pos_iff_exists_offCriticalZero.1 henergy
    have hcentral : (xiCentralReciprocalSquare (ρ : ℂ)).im ≠ 0 :=
      (xiCentralReciprocalSquare_im_eq_zero_iff ρ).not.2 hρ
    exact ⟨hnotOperator, hnotClifford, hnotDefects, hnotFixedSource, ⟨ρ, hcentral⟩,
      hnotTarget, hnotSource⟩
  · intro hcertificate hRH
    exact hcertificate.1 (xiReciprocalOperator_isSelfAdjoint_iff_rh.2 hRH)

end

end RHTower
