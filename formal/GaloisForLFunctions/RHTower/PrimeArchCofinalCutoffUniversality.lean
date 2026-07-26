import GaloisForLFunctions.RHTower.CCMPrimeGammaSourceEnergySpectrum
import GaloisForLFunctions.RHTower.CCMRectangularFullObservableDivisorTomography
import GaloisForLFunctions.RHTower.PrimeArchEndpointHausdorffTemperatureMaster
import GaloisForLFunctions.RHTower.PrimeArchThermalSoninDeterminantEndpointUniversalityLaw

/-!
# Cofinal cutoff elimination for prime--Gamma source criteria

Rectangular source theorems use an integer cutoff satisfying the eventual logarithmic aperture
condition.  That condition is automatic and cofinal.  This file removes it from the public
criteria and records that every sufficiently late prime--Gamma tail carries the same RH,
Hausdorff, finite-KMS, and coupled-Sonin phase.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Admissibility is cofinal in the cutoff: every sufficiently large tail index supports the
fixed rectangular window. -/
theorem eventually_xiRectangularAdmissibleCutoff (L : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2 := by
  obtain ⟨N₀, hN₀⟩ := exists_xiRectangularAdmissibleCutoff L
  filter_upwards [eventually_ge_atTop N₀] with N hN
  intro n hNn
  exact hN₀ n (hN.trans hNn)

/-- Every sufficiently late prime--Gamma negative tail has critical abscissa at most one exactly
when RH holds.  No cutoff witness remains in the statement. -/
theorem eventually_riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop,
      RiemannHypothesis ↔
        LSeries.abscissaOfAbsConv
            (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) := by
  filter_upwards [eventually_xiRectangularAdmissibleCutoff L] with N hN
  exact riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one hL hN

/-- The endpoint Hausdorff source--temperature master law holds at every sufficiently late
rectangular cutoff, with admissibility discharged once and for all. -/
theorem eventually_primeArchEndpointHausdorffSourceTemperatureMaster
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop,
      (∀ k r : ℕ,
        scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment k r =
          (∑' q : XiZeroCopy,
            xiZeroCopyReciprocalSquare q ^ (k + 1) *
              ((primeArchEndpointHausdorffRadius : ℂ) -
                xiZeroCopyReciprocalSquare q) ^ r).re) ∧
      (∀ k r : ℕ, k ≤ 13 → r ≤ 43 →
        0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment k r) ∧
      (PrimeArchEndpointHausdorffTailNonnegative ↔ RiemannHypothesis) ∧
      (LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
            ((1 : ℝ) : EReal) ↔ PrimeArchEndpointHausdorffTailNonnegative) ∧
      (PrimeArchEndpointHausdorffTailNonnegative ↔
        NonnegativeDirichletSummatoryGrowthAt
          (rectangularPrimePolarSourceTailNegativePart L N) 1) ∧
      (PrimeArchEndpointHausdorffTailNonnegative ↔
        PrimeArchFiniteKMSWightmanLocalMomentClosure) := by
  filter_upwards [eventually_xiRectangularAdmissibleCutoff L] with N hN
  exact primeArchEndpointHausdorffSourceTemperatureMaster hL hN

/-- Every sufficiently late literal prime--polar tail, every endpoint Hausdorff tail, finite KMS
closure, and the full coupled-Sonin thermal certificate lie in one exact phase. -/
theorem eventually_primeArchCofinalCutoffUniversalPhase
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop,
      (RiemannHypothesis ↔
        LSeries.abscissaOfAbsConv
            (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal)) ∧
      (RiemannHypothesis ↔
        LSeries.abscissaOfAbsConv
            (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal)) ∧
      (LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
            ((1 : ℝ) : EReal) ↔
        PrimeArchEndpointHausdorffTailNonnegative) ∧
      (LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
            ((1 : ℝ) : EReal) ↔
        PrimeArchFiniteKMSWightmanLocalMomentClosure) ∧
      (LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
            ((1 : ℝ) : EReal) ↔
        XiPrimeArchThermalSoninEndpointUniversalCertificate) := by
  filter_upwards [eventually_xiRectangularAdmissibleCutoff L] with N hN
  exact ⟨
    riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one hL hN,
    riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one hL hN,
    rectangularPrimePolarSource_negativeAbscissa_le_one_iff_rectangleHausdorffTailNonnegative
      hL hN,
    rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFiniteKMSLocalClosure
      hL hN,
    rectangularPrimePolarSource_negativeAbscissa_le_one_iff_thermalSoninEndpointCertificate
      hL hN⟩

end

end RHTower
