import GaloisForLFunctions.RHTower.ReflectedLambertRHBarrier
import GaloisForLFunctions.RHTower.CCMRectangularFullObservableDivisorTomography
import GaloisForLFunctions.RHTower.CCMPrimeGammaSourceDivisorTomography
import GaloisForLFunctions.RHTower.CCMCumulativeNegativeMassSpectrum
import GaloisForLFunctions.RHTower.CCMSmoothTwoEdgeWeil

/-!
# Local-to-global RH tomography

Publication capstone joining two unconditional theorem surfaces:

* the cofinite reflected-Lambert local-factor orbit and its continuous
  compact-open classifier obstruction;
* fixed-width logarithmic Weil tomography and its exact finite
  prime--Gamma source realization.

The first surface proves that a continuous finite-factor-invariant local
germ cannot classify the source Hankel sign.  The second supplies a global
weighted-tail observable which is RH-complete and recovers the full
off-critical divisor with analytic multiplicity.
-/

noncomputable section

namespace RHTower

/-- The local source-Hankel sign and every positive-width rectangular
logarithmic Weil sequence are exact RH classifiers.  Their information
behavior differs: the former cannot descend through the continuous
finite-factor local quotient, whereas the latter retains the global
weighted tail. -/
theorem localGlobal_two_exact_RH_classifiers
    {L : ℝ} (hL : 0 < L) :
    (PrimeArchSourceTraceHankelIntNonnegative ↔ RiemannHypothesis) ∧
    (RiemannHypothesis ↔
      ∀ n : ℕ, 0 ≤
        (xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re) := by
  exact ⟨reflectedLambert_sourceHankel_iff_RH,
    riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL⟩

/-- Deprecated exact alias; use
`riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow`. -/
@[deprecated riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow (since := "2026-08-22")]
theorem localGlobal_fixedWidth_eventualLowerBound_iff_RH
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        L ≤ Real.log n / 2 →
        B ≤ (xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re :=
  riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow hL

end RHTower
