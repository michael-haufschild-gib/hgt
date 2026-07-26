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

/-- Generic elimination rule for every theorem whose only cutoff premise is rectangular
admissibility. -/
theorem eventually_of_xiRectangularAdmissibleCutoff
    (L : ℝ) {P : ℕ → Prop}
    (h : ∀ N : ℕ, (∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) → P N) :
    ∀ᶠ N : ℕ in atTop, P N := by
  filter_upwards [eventually_xiRectangularAdmissibleCutoff L] with N hN
  exact h N hN

/-- The equivalent doubled-window form used by critical Mellin remainder theorems is also
automatic at every sufficiently late cutoff. -/
theorem eventually_xiRectangularDoubleWidthAdmissibleCutoff (L : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N ≤ n →
      2 * L ≤ Real.log n := by
  filter_upwards [eventually_xiRectangularAdmissibleCutoff L] with N hN
  intro n hn
  linarith [(hN n hn).2]

/-- The single-log aperture form used by sharp-window source theorems is automatic at every
sufficiently late cutoff. -/
theorem eventually_xiLogWindowAdmissibleCutoff (L : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N ≤ n →
      L ≤ Real.log n := by
  filter_upwards [eventually_xiRectangularAdmissibleCutoff L] with N hN
  intro n hn
  have hlog : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (hN n hn).1)
  linarith [(hN n hn).2]

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

/-- Joint phase carried by one rectangular cutoff: Xi-divisor and literal prime--polar
abscissae, the endpoint Hausdorff tail, finite KMS closure, and the coupled-Sonin thermal
certificate all classify the same source. -/
def PrimeArchCofinalCutoffUniversalCertificate (L : ℝ) (N : ℕ) : Prop :=
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
    XiPrimeArchThermalSoninEndpointUniversalCertificate)

/-- Every sufficiently late literal prime--polar tail, every endpoint Hausdorff tail, finite KMS
closure, and the full coupled-Sonin thermal certificate lie in one exact phase. -/
theorem eventually_primeArchCofinalCutoffUniversalPhase
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop,
      PrimeArchCofinalCutoffUniversalCertificate L N := by
  filter_upwards [eventually_xiRectangularAdmissibleCutoff L] with N hN
  rw [PrimeArchCofinalCutoffUniversalCertificate]
  exact ⟨
    riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one hL hN,
    riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one hL hN,
    rectangularPrimePolarSource_negativeAbscissa_le_one_iff_rectangleHausdorffTailNonnegative
      hL hN,
    rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFiniteKMSLocalClosure
      hL hN,
    rectangularPrimePolarSource_negativeAbscissa_le_one_iff_thermalSoninEndpointCertificate
      hL hN⟩

/-- Fully unconditional unit-width source theorem: every sufficiently late cutoff carries the
joint prime--Gamma/Hausdorff/KMS/Sonin phase certificate. -/
theorem eventually_primeArchUnitWidthCofinalCutoffUniversalCertificate :
    ∀ᶠ N : ℕ in atTop, PrimeArchCofinalCutoffUniversalCertificate 1 N :=
  eventually_primeArchCofinalCutoffUniversalPhase (by norm_num)

/-- A concrete tail source carrying the complete joint phase exists without any analytic,
arithmetic, or cutoff premise. -/
theorem exists_primeArchUnitWidthCofinalCutoffUniversalCertificate :
    ∃ N : ℕ, PrimeArchCofinalCutoffUniversalCertificate 1 N := by
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.1 eventually_primeArchUnitWidthCofinalCutoffUniversalCertificate
  exact ⟨N₀, hN₀ N₀ le_rfl⟩

end

end RHTower
