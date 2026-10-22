import GaloisForLFunctions.RHTower.Deninger.DeningerClosedGeneratorHodgeWeilPurityUniversalityLaw
import GaloisForLFunctions.RHTower.CCM.CCMMultiplicativeFirstClockVolterraCurvatureUniversalityLaw

/-!
# Deninger-Hodge first-clock Volterra-curvature universality

The Deninger-Hodge purity phases force full Weil-square positivity.  The multiplicative
first-clock identity transports that positivity to the exact Volterra-corrected curvature of the
physical first clock at every admissible pair of integer apertures.
-/

namespace RHTower

noncomputable section

/-- Exact complex multiplicative midpoint curvature of the Volterra-corrected first clock. -/
def ccmFirstClockVolterraMultiplicativeCurvatureValue (m n : ℕ) : ℂ :=
  2 *
    ((ccmFirstClockXiRationalDivisor (Real.log ((m ^ 2 * n : ℕ) : ℝ)) -
        ccmFirstClockXiVolterraMemory (Real.log ((m ^ 2 * n : ℕ) : ℝ))) +
      (ccmFirstClockXiRationalDivisor (Real.log n) -
        ccmFirstClockXiVolterraMemory (Real.log n)) -
      2 * (ccmFirstClockXiRationalDivisor (Real.log ((m * n : ℕ) : ℝ)) -
        ccmFirstClockXiVolterraMemory (Real.log ((m * n : ℕ) : ℝ))) +
      2 * (ccmFirstClockXiRationalDivisor (Real.log m) -
        ccmFirstClockXiVolterraMemory (Real.log m)))

/-- Nonnegative real multiplicative curvature throughout the physical first-clock aperture range. -/
def CCMFirstClockVolterraMultiplicativeCurvatureNonnegative : Prop :=
  ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n →
    Real.pi / 2 ≤ Real.log m →
    Real.pi / 2 ≤ Real.log n →
    Real.pi / 2 ≤ Real.log ((m * n : ℕ) : ℝ) →
    Real.pi / 2 ≤ Real.log ((m ^ 2 * n : ℕ) : ℝ) →
      0 ≤ (ccmFirstClockVolterraMultiplicativeCurvatureValue m n).re

/-- Full Weil-square positivity forces every physical first-clock multiplicative curvature sign. -/
theorem xiWeilSquareConeNonnegative_firstClockVolterraMultiplicativeCurvature
    (hWeil : XiWeilSquareConeNonnegative) :
    CCMFirstClockVolterraMultiplicativeCurvatureNonnegative := by
  intro m n hm hn hLm hLn hLmn hLm2n
  have hnonneg :=
    hWeil
      (xiRectangularTwoEdgeTransform (Real.log m)
        (Real.log ((m ^ 2 * n : ℕ) : ℝ) / 2))
      (xiRectangularTwoEdgeTransform_squareSummable
        (Real.log m) (Real.log ((m ^ 2 * n : ℕ) : ℝ) / 2))
  rw [xiWeilPolarization_rectangular_log_mul_sq_eq_firstClockVolterraCurvature
    hm hn hLm hLn hLmn hLm2n] at hnonneg
  simpa only [ccmFirstClockVolterraMultiplicativeCurvatureValue] using hnonneg

/-- Joint closed-generator purity and first-clock Volterra-curvature certificate. -/
structure DeningerHodgeFirstClockVolterraCurvatureCertificate : Prop where
  purity : DeningerClosedGeneratorHodgeWeilPurityCertificate
  rectangularIdentity :
    ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n →
      Real.pi / 2 ≤ Real.log m →
      Real.pi / 2 ≤ Real.log n →
      Real.pi / 2 ≤ Real.log ((m * n : ℕ) : ℝ) →
      Real.pi / 2 ≤ Real.log ((m ^ 2 * n : ℕ) : ℝ) →
        xiWeilPolarization
            (xiRectangularTwoEdgeTransform (Real.log m)
              (Real.log ((m ^ 2 * n : ℕ) : ℝ) / 2))
            (xiRectangularTwoEdgeTransform (Real.log m)
              (Real.log ((m ^ 2 * n : ℕ) : ℝ) / 2)) =
          ccmFirstClockVolterraMultiplicativeCurvatureValue m n
  weilForcesCurvature :
    XiWeilSquareConeNonnegative →
      CCMFirstClockVolterraMultiplicativeCurvatureNonnegative
  rhForcesCurvature :
    RiemannHypothesis →
      CCMFirstClockVolterraMultiplicativeCurvatureNonnegative
  localHodgeForcesCurvature :
    DeningerLocalJetHodgeFrobeniusInvariant →
      CCMFirstClockVolterraMultiplicativeCurvatureNonnegative
  finiteHodgeForcesCurvature :
    DeningerFiniteJetHodgeExhaustionFrobeniusInvariant →
      CCMFirstClockVolterraMultiplicativeCurvatureNonnegative

/--
**Deninger-Hodge first-clock Volterra-curvature universality law.**

Every equivalent Deninger-Hodge/Weil purity phase forces nonnegative real multiplicative curvature
of the exact Volterra-corrected first-clock carrier at every physical integer aperture.
-/
theorem deningerHodge_firstClockVolterraCurvatureUniversality :
    DeningerHodgeFirstClockVolterraCurvatureCertificate := by
  have hpurity := deningerClosedGenerator_hodgeWeilPurityUniversality
  have hforce :=
    xiWeilSquareConeNonnegative_firstClockVolterraMultiplicativeCurvature
  exact
    { purity := hpurity
      rectangularIdentity := fun m n hm hn hLm hLn hLmn hLm2n =>
        (xiWeilPolarization_rectangular_log_mul_sq_eq_firstClockVolterraCurvature
          hm hn hLm hLn hLmn hLm2n).trans rfl
      weilForcesCurvature := hforce
      rhForcesCurvature := fun hRH =>
        hforce
          (riemannHypothesis_iff_xiWeilSquareConeNonnegative.mp hRH)
      localHodgeForcesCurvature := fun hlocal =>
        hforce
          (riemannHypothesis_iff_xiWeilSquareConeNonnegative.mp
            (hpurity.localHodgeIffRH.mp hlocal))
      finiteHodgeForcesCurvature := fun hfinite =>
        hforce
          (riemannHypothesis_iff_xiWeilSquareConeNonnegative.mp
            (hpurity.finitePacketsIffRH.mp hfinite)) }

end

end RHTower
