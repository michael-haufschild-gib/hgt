import GaloisForLFunctions.RHTower.CCM.CCMRectangularObservableHolomorphicCriterion
import GaloisForLFunctions.RHTower.CCM.CCMSmoothTwoEdgeWeil
import GaloisForLFunctions.RHTower.CCM.CCMUnconditionalFoundation
import GaloisForLFunctions.RHTower.CCM.CCMUniversalWeilSourceReconstruction
import GaloisForLFunctions.RHTower.PrimeArchBernsteinAbelMeromorphicCollarCriterion
import GaloisForLFunctions.RHTower.PrimeArchEndpointHausdorffTemperatureMaster
import GaloisForLFunctions.RHTower.PrimeArchSourceLocalBoundGate
import GaloisForLFunctions.RHTower.SoninCoupledVarianceCollapse
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCurrentRemainderEquivalence
import GaloisForLFunctions.RHTower.XiPositivePairedDiagonalSectorCollapse

/-!
# Xi terminal analytic-source universality

Ten previously terminal mechanisms encode one analytic-source phase: rectangular tail
continuation, smooth two-edge Weil control, global and rank-two CCM passivity, separated source
reconstruction, prime--archimedean collar/Hausdorff/local control, coupled Sonin variance,
finite-arithmetic Taylor-current control, and the positive-paired exterior diagonal.
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Simultaneous realization of the Xi phase in fourteen terminal analytic and source charts. -/
def XiTerminalAnalyticSourceUniversalCertificate
    (Lrect : ℝ) (N : ℕ) (eta Lsmooth : ℝ)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (D : ℕ → ℕ) (degreeSet : Set ℕ) : Prop :=
  XiRectangularWeilTailHolomorphicContinuation Lrect N ∧
  (∀ (f : SmoothBoundaryProfile eta Lsmooth) (n : ℕ),
    Lsmooth < Real.log n / 2 →
    0 ≤ (xiWeilPolarization
      (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
      (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re) ∧
  (∀ f : SmoothBoundaryProfile eta Lsmooth,
    ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      Lsmooth < Real.log n / 2 →
      B ≤ (xiWeilPolarization
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re) ∧
  CCMGlobalWeilPassivity ∧
  CCMRegularTwoPolePassivity ∧
  CCMContinuedTwoPoleSourcePassivity ∧
  (∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → B ≤ (P n).sourceEnergy) ∧
  PrimeArchEndpointBernsteinAbelMeromorphicCollar ∧
  PrimeArchEndpointHausdorffTailNonnegative ∧
  CompletedPrimeGammaLeftHalfLocallyBoundedBelow ∧
  SoninCoupledPrimeArchNormalizedVarianceUpperBound ∧
  SoninCoupledPrimeArchCenteredTwoEisensteinResidualNormalizedVarianceUpperBound degreeSet ∧
  XiCTaylorThetaTailCoreCurrentJointSublinearUpper
    (1 / 8 : ℝ) (1 / 4 : ℝ) D
    canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
    canonicalThetaTailCoreFiniteArithmeticRemainderCurrent ∧
  ContinuedPrimeArchPositiveExteriorPairedDiagonalNonnegative (218 / 25)

/-- **Terminal analytic-source universality law.**  Under the source admissibility hypotheses,
RH is equivalent to simultaneous realization in all fourteen terminal analytic-source charts. -/
theorem riemannHypothesis_iff_terminalAnalyticSourceUniversalCertificate
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite) :
    RiemannHypothesis ↔
      XiTerminalAnalyticSourceUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet := by
  constructor
  · intro hRH
    exact ⟨
      (xiRectangularWeilTailHolomorphicContinuation_iff_riemannHypothesis
        hLrect hN).2 hRH,
      (riemannHypothesis_iff_smoothProfile_logSample_weil_nonneg
        heta hwindow).1 hRH,
      (riemannHypothesis_iff_smoothProfile_logSample_weil_eventually_bddBelow
        heta hwindow).1 hRH,
      ccmGlobalWeilPassivity_iff_riemannHypothesis.2 hRH,
      ccmRegularTwoPolePassivity_iff_riemannHypothesis.2 hRH,
      ccmContinuedTwoPoleSourcePassivity_iff_riemannHypothesis.2 hRH,
      (riemannHypothesis_iff_rectangularSeparatedSourceSection_eventually_bddBelow
        hLrect P hP).1 hRH,
      primeArchEndpointBernsteinAbelMeromorphicCollar_iff_riemannHypothesis.2 hRH,
      primeArchEndpointHausdorffTailNonnegative_iff_riemannHypothesis.2 hRH,
      completedPrimeGammaLeftHalfLocallyBoundedBelow_iff_riemannHypothesis.2 hRH,
      soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis.2 hRH,
      (soninCoupledPrimeArchCenteredTwoEisensteinResidualUpper_iff_riemannHypothesis
        hdegreeSet).2 hRH,
      (xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis
        hD).2 hRH,
      continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_twoHundredEighteen_twentyFifths_iff_rh.2
        hRH⟩
  · intro hcertificate
    exact (xiRectangularWeilTailHolomorphicContinuation_iff_riemannHypothesis
      hLrect hN).1 hcertificate.1

/-- Simultaneous failure of all fourteen terminal analytic and source charts. -/
def XiTerminalAnalyticSourceFailureUniversalCertificate
    (Lrect : ℝ) (N : ℕ) (eta Lsmooth : ℝ)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (D : ℕ → ℕ) (degreeSet : Set ℕ) : Prop :=
  (¬ XiRectangularWeilTailHolomorphicContinuation Lrect N) ∧
  (¬ ∀ (f : SmoothBoundaryProfile eta Lsmooth) (n : ℕ),
    Lsmooth < Real.log n / 2 →
    0 ≤ (xiWeilPolarization
      (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
      (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re) ∧
  (¬ ∀ f : SmoothBoundaryProfile eta Lsmooth,
    ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      Lsmooth < Real.log n / 2 →
      B ≤ (xiWeilPolarization
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re) ∧
  (¬ CCMGlobalWeilPassivity) ∧
  (¬ CCMRegularTwoPolePassivity) ∧
  (¬ CCMContinuedTwoPoleSourcePassivity) ∧
  (¬ ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → B ≤ (P n).sourceEnergy) ∧
  (¬ PrimeArchEndpointBernsteinAbelMeromorphicCollar) ∧
  (¬ PrimeArchEndpointHausdorffTailNonnegative) ∧
  (¬ CompletedPrimeGammaLeftHalfLocallyBoundedBelow) ∧
  (¬ SoninCoupledPrimeArchNormalizedVarianceUpperBound) ∧
  (¬ SoninCoupledPrimeArchCenteredTwoEisensteinResidualNormalizedVarianceUpperBound degreeSet) ∧
  (¬ XiCTaylorThetaTailCoreCurrentJointSublinearUpper
    (1 / 8 : ℝ) (1 / 4 : ℝ) D
    canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
    canonicalThetaTailCoreFiniteArithmeticRemainderCurrent) ∧
  (¬ ContinuedPrimeArchPositiveExteriorPairedDiagonalNonnegative (218 / 25))

/-- **Synchronized terminal analytic-source failure law.** -/
theorem not_riemannHypothesis_iff_terminalAnalyticSourceFailureUniversalCertificate
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite) :
    ¬ RiemannHypothesis ↔
      XiTerminalAnalyticSourceFailureUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet := by
  constructor
  · intro hnotRH
    exact ⟨
      fun h => hnotRH ((xiRectangularWeilTailHolomorphicContinuation_iff_riemannHypothesis
        hLrect hN).1 h),
      fun h => hnotRH ((riemannHypothesis_iff_smoothProfile_logSample_weil_nonneg
        heta hwindow).2 h),
      fun h => hnotRH ((riemannHypothesis_iff_smoothProfile_logSample_weil_eventually_bddBelow
        heta hwindow).2 h),
      fun h => hnotRH (ccmGlobalWeilPassivity_iff_riemannHypothesis.1 h),
      fun h => hnotRH (ccmRegularTwoPolePassivity_iff_riemannHypothesis.1 h),
      fun h => hnotRH (ccmContinuedTwoPoleSourcePassivity_iff_riemannHypothesis.1 h),
      fun h => hnotRH
        ((riemannHypothesis_iff_rectangularSeparatedSourceSection_eventually_bddBelow
          hLrect P hP).2 h),
      fun h => hnotRH
        (primeArchEndpointBernsteinAbelMeromorphicCollar_iff_riemannHypothesis.1 h),
      fun h => hnotRH (primeArchEndpointHausdorffTailNonnegative_iff_riemannHypothesis.1 h),
      fun h => hnotRH
        (completedPrimeGammaLeftHalfLocallyBoundedBelow_iff_riemannHypothesis.1 h),
      fun h => hnotRH
        (soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis.1 h),
      fun h => hnotRH
        ((soninCoupledPrimeArchCenteredTwoEisensteinResidualUpper_iff_riemannHypothesis
          hdegreeSet).1 h),
      fun h => hnotRH
        ((xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis
          hD).1 h),
      fun h => hnotRH
        (continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_twoHundredEighteen_twentyFifths_iff_rh.1
          h)⟩
  · intro hcertificate hRH
    exact hcertificate.1
      ((xiRectangularWeilTailHolomorphicContinuation_iff_riemannHypothesis
        hLrect hN).2 hRH)

end

end RHTower
