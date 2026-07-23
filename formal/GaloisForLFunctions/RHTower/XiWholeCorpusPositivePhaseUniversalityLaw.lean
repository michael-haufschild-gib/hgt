import GaloisForLFunctions.RHTower.XiCassiniThetaReciprocalSourceUniversalityLaw
import GaloisForLFunctions.RHTower.XiCountableHankelTestSetUniversalityLaw
import GaloisForLFunctions.RHTower.XiDyadicDescentLevelUniversalityLaw
import GaloisForLFunctions.RHTower.XiEuclideanKrylovJensenReflectionUniversalityLaw
import GaloisForLFunctions.RHTower.XiHedenmalmOrientationEndpointUniversalityLaw
import GaloisForLFunctions.RHTower.XiHurwitzOrientationUniversalityLaw
import GaloisForLFunctions.RHTower.XiLocalAnalyticOrderPhaseUniversalityLaw
import GaloisForLFunctions.RHTower.XiPrimeArchThermalEndpointUniversalityLaw
import GaloisForLFunctions.RHTower.XiPrimeSeamCalkinUniversalityLaw
import GaloisForLFunctions.RHTower.XiReciprocalFixedCauchyKrylovSourceUniversalityLaw
import GaloisForLFunctions.RHTower.XiReciprocalSquareSourceUniversalityLaw
import GaloisForLFunctions.RHTower.XiSquaredEulerDiagonalCorrelationUniversalityLaw
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniDyadicUniversalityLaw
import GaloisForLFunctions.RHTower.XiTerminalAnalyticSourceUniversalityLaw
import GaloisForLFunctions.RHTower.XiTerminalGeometricPhaseUniversalityLaw
import GaloisForLFunctions.RHTower.XiZeroLocalCriticalPhaseUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion

/-!
# Whole-corpus Xi positive-phase universality

The terminal Xi corpus had many maximal certificates, each closing a different theorem family,
but no theorem synchronized those capstones themselves.  This file forms the parameter-uniform
positive product over all currently terminal certificate families that are equivalent to RH.
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Simultaneous positive realization in all currently terminal global, levelwise, and local Xi
certificate families. -/
structure XiWholeCorpusPositivePhaseUniversalCertificate
    (Lrect : ℝ) (N : ℕ) (eta Lsmooth : ℝ)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (D : ℕ → ℕ) (degreeSet : Set ℕ) (prime : Nat.Primes) (q : ℕ) : Prop where
  analyticSource :
    XiTerminalAnalyticSourceUniversalCertificate
      Lrect N eta Lsmooth P D degreeSet
  geometricPhase : XiTerminalGeometricPhaseUniversalCertificate
  countableHankelTestSets : XiCountableHankelTestSetUniversalCertificate
  primeArchHankelExactReconstruction :
    PrimeArchSourceMomentHankelExactReconstructionPhase
  allDyadicDescentLevels :
    ∀ k : ℕ, XiDyadicDescentLevelUniversalCertificate k
  euclideanKrylovJensenReflection :
    XiEuclideanKrylovJensenReflectionUniversalCertificate
  hedenmalmOrientationEndpoint :
    XiHedenmalmOrientationEndpointUniversalCertificate
  allRightZeroLocalAnalyticPhases :
    ∀ rho ∈ rightHalf, xi rho = 0 →
      XiLocalAnalyticOrderPhaseUniversalCertificate prime q rho
  primeSeamCalkin : XiPrimeSeamCalkinUniversalCertificate
  reciprocalSquareSource : XiReciprocalSquareSourceUniversalCertificate
  squaredEulerDiagonalCorrelation :
    XiSquaredEulerDiagonalCorrelationUniversalCertificate
  cassiniThetaReciprocalSource :
    XiCassiniThetaReciprocalSourceUniversalCertificate
  squaredSeamCassiniDyadic : XiSquaredSeamCassiniDyadicUniversalCertificate
  hurwitzOrientation : XiHurwitzOrientationUniversalCertificate
  primeArchThermalEndpoint : XiPrimeArchThermalEndpointUniversalCertificate
  fixedCauchyKrylovSaturation :
    XiReciprocalSquareFixedCauchyKrylovSourceContrastSaturation
  everyZeroLocalCriticalPhase :
    ∀ rho : ℂ, xi rho = 0 → ∀ p : ℕ, 1 < p → ∀ a : ℝ,
      XiZeroLocalCriticalPhaseUniversalCertificate rho p a

/-- **Whole-corpus Xi positive-phase universality law.**  Under only the parameter admissibility
needed by the analytic-source and thermal capstones, RH is equivalent to simultaneous realization
of all seventeen currently terminal certificate families.  These include global certificates,
every dyadic depth, every right-half zero, and every actual zero with every admissible prime-mark
base and Clifford weight. -/
theorem riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    RiemannHypothesis ↔
      XiWholeCorpusPositivePhaseUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet prime q := by
  constructor
  · intro hRH
    refine {
      analyticSource :=
        (riemannHypothesis_iff_terminalAnalyticSourceUniversalCertificate
          hLrect hN heta hwindow P hP hD hdegreeSet).1 hRH
      geometricPhase :=
        riemannHypothesis_iff_terminalGeometricPhaseUniversalCertificate.1 hRH
      countableHankelTestSets :=
        riemannHypothesis_iff_countableHankelTestSetUniversalCertificate.1 hRH
      primeArchHankelExactReconstruction :=
        primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis.2 hRH
      allDyadicDescentLevels :=
        riemannHypothesis_iff_forall_dyadicDescentLevelUniversalCertificate.1 hRH
      euclideanKrylovJensenReflection :=
        riemannHypothesis_iff_euclideanKrylovJensenReflectionUniversalCertificate.1 hRH
      hedenmalmOrientationEndpoint :=
        riemannHypothesis_iff_hendenmalmOrientationEndpointUniversalCertificate.1 hRH
      allRightZeroLocalAnalyticPhases :=
        (riemannHypothesis_iff_all_rightZeros_localPhaseUniversalCertificate
          prime hq).1 hRH
      primeSeamCalkin :=
        (xiPrimeTwoThreeSeamNormsEqual_iff_riemannHypothesis.symm.trans
          xiPrimeTwoThreeSeamNormsEqual_iff_calkinUniversalCertificate).1 hRH
      reciprocalSquareSource :=
        (xiReciprocalSquareOperator_isSelfAdjoint_iff_riemannHypothesis.symm.trans
          xiReciprocalSquareOperator_isSelfAdjoint_iff_sourceUniversalCertificate).1 hRH
      squaredEulerDiagonalCorrelation :=
        (xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.symm.trans
          xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_universalCertificate).1 hRH
      cassiniThetaReciprocalSource :=
        (thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis.symm.trans
          thetaCuspCassiniInwardBoundarySaturated_iff_reciprocalSourceUniversalCertificate).1 hRH
      squaredSeamCassiniDyadic :=
        (xiSquaredSeamPowerSixtyFourSourceDominated_iff_riemannHypothesis.symm.trans
          xiSquaredSeamPowerSixtyFourSourceDominated_iff_cassiniDyadicUniversalCertificate).1 hRH
      hurwitzOrientation :=
        (riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.trans
          xiHurwitzOrientationEnergy_eq_zero_iff_universalCertificate).1 hRH
      primeArchThermalEndpoint :=
        ((riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
            hLrect hN).trans
          (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_endpointUniversalCertificate
            hLrect hN)).1 hRH
      fixedCauchyKrylovSaturation :=
        xiReciprocalSquareFixedCauchyKrylovSourceContrastSaturation_iff_riemannHypothesis.2 hRH
      everyZeroLocalCriticalPhase := by
        intro rho hzero p hp a
        exact (xiZero_re_eq_half_iff_localCriticalPhaseUniversalCertificate
          hzero hp a).1 (xi_zero_re_eq_half_of_RH hRH hzero) }
  · intro hcertificate
    exact riemannHypothesis_iff_terminalGeometricPhaseUniversalCertificate.2
      hcertificate.geometricPhase

/-- Simultaneous negative realization in all terminal certificate families possessing a global
failure chart, together with explicit failure of the remaining positive-only capstones. -/
structure XiWholeCorpusFailurePhaseUniversalCertificate
    (Lrect : ℝ) (N : ℕ) (eta Lsmooth : ℝ)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (D : ℕ → ℕ) (degreeSet : Set ℕ) (prime : Nat.Primes) (q : ℕ)
    (aperture : ℝ) : Prop where
  analyticSourceFailure :
    XiTerminalAnalyticSourceFailureUniversalCertificate
      Lrect N eta Lsmooth P D degreeSet
  geometricPhaseFailure : XiTerminalGeometricPhaseFailureUniversalCertificate
  countableHankelFailure : XiCountableHankelTestSetFailureUniversalCertificate
  primeArchHankelExactReconstructionFails :
    ¬PrimeArchSourceMomentHankelExactReconstructionPhase
  someDyadicDescentLevelFails :
    ∃ k : ℕ, ¬XiDyadicDescentLevelUniversalCertificate k
  euclideanKrylovJensenFailure :
    XiEuclideanKrylovJensenReflectionFailureUniversalCertificate
  hedenmalmOrientationFailure :
    XiHedenmalmOrientationEndpointFailureUniversalCertificate
  rightZeroLocalAnalyticPhaseFails :
    ¬(∀ rho ∈ rightHalf, xi rho = 0 →
      XiLocalAnalyticOrderPhaseUniversalCertificate prime q rho)
  primeSeamCalkinFailure :
    XiPrimeSeamCalkinFailureUniversalCertificate aperture
  reciprocalSquareSourceFailure :
    XiReciprocalSquareSourceFailureUniversalCertificate
  squaredEulerDiagonalCorrelationFailure :
    XiSquaredEulerDiagonalCorrelationFailureUniversalCertificate
  cassiniThetaReciprocalSourceFailure :
    XiCassiniThetaReciprocalSourceFailureUniversalCertificate
  squaredSeamCassiniDyadicFailure :
    XiSquaredSeamCassiniDyadicFailureUniversalCertificate
  hurwitzOrientationFailure : XiHurwitzOrientationFailureUniversalCertificate
  primeArchThermalEndpointFails :
    ¬XiPrimeArchThermalEndpointUniversalCertificate
  fixedCauchyKrylovPositiveFailure :
    XiReciprocalSquareFixedCauchyKrylovSourceContrastPositiveFailure

/-- **Whole-corpus Xi failure-phase universality law.**  Failure of RH is equivalent to
simultaneous failure realization in every terminal family with a global negative chart, failure
of some dyadic level and the all-right-zero local phase, and strict positive fixed-Cauchy Krylov
contrast. -/
theorem not_riemannHypothesis_iff_wholeCorpusFailurePhaseUniversalCertificate
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0)
    {aperture : ℝ} (haperture : 0 < aperture) :
    ¬RiemannHypothesis ↔
      XiWholeCorpusFailurePhaseUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet prime q aperture := by
  constructor
  · intro hnotRH
    refine {
      analyticSourceFailure :=
        (not_riemannHypothesis_iff_terminalAnalyticSourceFailureUniversalCertificate
          hLrect hN heta hwindow P hP hD hdegreeSet).1 hnotRH
      geometricPhaseFailure :=
        not_riemannHypothesis_iff_terminalGeometricPhaseFailureUniversalCertificate.1 hnotRH
      countableHankelFailure :=
        not_riemannHypothesis_iff_countableHankelTestSetFailureUniversalCertificate.1 hnotRH
      primeArchHankelExactReconstructionFails := fun hexact =>
        hnotRH
          (primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis.1
            hexact)
      someDyadicDescentLevelFails := by
        by_contra hnoFailure
        apply hnotRH
        apply riemannHypothesis_iff_forall_dyadicDescentLevelUniversalCertificate.2
        intro k
        by_contra hk
        exact hnoFailure ⟨k, hk⟩
      euclideanKrylovJensenFailure :=
        not_riemannHypothesis_iff_euclideanKrylovJensenReflectionFailureUniversalCertificate.1
          hnotRH
      hedenmalmOrientationFailure :=
        not_riemannHypothesis_iff_hendenmalmOrientationEndpointFailureUniversalCertificate.1
          hnotRH
      rightZeroLocalAnalyticPhaseFails := by
        intro hall
        exact hnotRH
          ((riemannHypothesis_iff_all_rightZeros_localPhaseUniversalCertificate
            prime hq).2 hall)
      primeSeamCalkinFailure :=
        (not_riemannHypothesis_iff_primeSeamCalkinFailureUniversalCertificate
          aperture haperture).1 hnotRH
      reciprocalSquareSourceFailure :=
        not_riemannHypothesis_iff_reciprocalSquareSourceFailureUniversalCertificate.1 hnotRH
      squaredEulerDiagonalCorrelationFailure :=
        not_riemannHypothesis_iff_squaredEulerDiagonalCorrelationFailureUniversalCertificate.1
          hnotRH
      cassiniThetaReciprocalSourceFailure := by
        apply not_thetaCuspCassiniInwardBoundarySaturated_iff_reciprocalSourceFailureCertificate.1
        intro htheta
        exact hnotRH
          (thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis.1 htheta)
      squaredSeamCassiniDyadicFailure :=
        not_riemannHypothesis_iff_squaredSeamCassiniDyadicFailureUniversalCertificate.1 hnotRH
      hurwitzOrientationFailure :=
        (xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.symm.trans
          xiHurwitzOrientationEnergy_pos_iff_failureUniversalCertificate).1 hnotRH
      primeArchThermalEndpointFails := by
        intro hthermal
        apply hnotRH
        exact ((riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
            hLrect hN).trans
          (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_endpointUniversalCertificate
            hLrect hN)).2 hthermal
      fixedCauchyKrylovPositiveFailure :=
        xiReciprocalSquareFixedCauchyKrylovSourceContrastPositiveFailure_iff_not_riemannHypothesis.2
          hnotRH }
  · intro hcertificate
    exact not_riemannHypothesis_iff_terminalGeometricPhaseFailureUniversalCertificate.2
      hcertificate.geometricPhaseFailure

/-- Positive and negative whole-corpus phases are exact complements. -/
theorem not_wholeCorpusPositivePhase_iff_wholeCorpusFailurePhase
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0)
    {aperture : ℝ} (haperture : 0 < aperture) :
    (¬XiWholeCorpusPositivePhaseUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet prime q) ↔
      XiWholeCorpusFailurePhaseUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet prime q aperture :=
  (not_congr (riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate
    hLrect hN heta hwindow P hP hD hdegreeSet prime hq)).symm.trans
      (not_riemannHypothesis_iff_wholeCorpusFailurePhaseUniversalCertificate
        hLrect hN heta hwindow P hP hD hdegreeSet prime hq haperture)

end

end RHTower
