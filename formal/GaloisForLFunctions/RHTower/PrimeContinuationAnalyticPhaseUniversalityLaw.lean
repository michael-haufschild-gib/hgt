import GaloisForLFunctions.RHTower.BVPrimeWindowDivisorTomography
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowContinuation
import GaloisForLFunctions.RHTower.CCMSimplePrimeDivisorSource

/-!
# Prime-continuation analytic-phase universality

The dyadic sharp-prime continuation, the elementary simple-prime continuation, and every
noncensoring compact-BV prime-window continuation share one right-half-plane analytic phase.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Simultaneous right-half-plane holomorphy of the two fixed prime continuations and every
compact-BV continuation whose Mellin transform cannot censor a right-half-plane divisor. -/
def PrimeContinuationAnalyticPhaseUniversalCertificate : Prop :=
  AnalyticOnNhd ℂ dyadicSharpPrimeContinuedSource {s : ℂ | 1 < s.re} ∧
  AnalyticOnNhd ℂ simplePrimeDivisorContinuedSource {s : ℂ | 1 < s.re} ∧
  ∀ W : CompactBVPrimeWindow,
    (∀ s : ℂ, 1 < s.re → W.mellinTransform s ≠ 0) →
    AnalyticOnNhd ℂ W.continuedSource {s : ℂ | 1 < s.re}

/-- **Prime-continuation analytic-phase universality law.**  RH is exactly the common
right-half-plane holomorphic phase of the two fixed prime continuations and the complete
noncensoring compact-BV family. -/
theorem riemannHypothesis_iff_primeContinuationAnalyticPhaseUniversalCertificate :
    RiemannHypothesis ↔ PrimeContinuationAnalyticPhaseUniversalCertificate := by
  constructor
  · intro hRH
    exact ⟨
      riemannHypothesis_iff_dyadicSharpPrimeContinuedSource_analyticOn_rightOne.1 hRH,
      riemannHypothesis_iff_simplePrimeDivisorContinuedSource_analyticOn_rightOne.1 hRH,
      fun W hM =>
        (CompactBVPrimeWindow.riemannHypothesis_iff_continuedSource_analyticOn_rightOne
          W hM).1 hRH⟩
  · intro hcertificate
    exact
      riemannHypothesis_iff_dyadicSharpPrimeContinuedSource_analyticOn_rightOne.2
        hcertificate.1

/-- Simultaneous failure of right-half-plane holomorphy in every prime-continuation chart of the
universal certificate. -/
def PrimeContinuationNonanalyticPhaseUniversalCertificate : Prop :=
  (¬ AnalyticOnNhd ℂ dyadicSharpPrimeContinuedSource {s : ℂ | 1 < s.re}) ∧
  (¬ AnalyticOnNhd ℂ simplePrimeDivisorContinuedSource {s : ℂ | 1 < s.re}) ∧
  ∀ W : CompactBVPrimeWindow,
    (∀ s : ℂ, 1 < s.re → W.mellinTransform s ≠ 0) →
    ¬ AnalyticOnNhd ℂ W.continuedSource {s : ℂ | 1 < s.re}

/-- Failure of RH is exactly simultaneous non-holomorphy in all fixed and noncensoring
compact-BV prime-continuation charts. -/
theorem not_riemannHypothesis_iff_primeContinuationNonanalyticPhaseUniversalCertificate :
    ¬ RiemannHypothesis ↔ PrimeContinuationNonanalyticPhaseUniversalCertificate := by
  constructor
  · intro hnotRH
    refine ⟨?_, ?_, ?_⟩
    · intro han
      exact hnotRH
        (riemannHypothesis_iff_dyadicSharpPrimeContinuedSource_analyticOn_rightOne.2 han)
    · intro han
      exact hnotRH
        (riemannHypothesis_iff_simplePrimeDivisorContinuedSource_analyticOn_rightOne.2 han)
    · intro W hM han
      exact hnotRH
        ((CompactBVPrimeWindow.riemannHypothesis_iff_continuedSource_analyticOn_rightOne
          W hM).2 han)
  · intro hcertificate hRH
    exact hcertificate.1
      (riemannHypothesis_iff_dyadicSharpPrimeContinuedSource_analyticOn_rightOne.1 hRH)

end

end RHTower
