import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFullFormula
import GaloisForLFunctions.RHTower.CCMSourceDivisorEnergySpectrum

/-!
# Exact prime--Gamma source spectrum of the sharp rectangular Xi observable

The complete sharp rectangular Guinand--Weil formula identifies every admissible logarithmic
sample of the Xi polarization with a source expression containing only a finite von Mangoldt
autocorrelation and the completed Gamma integral.  This module makes that source sequence the
primary object and transports the complete horizontal-divisor spectrum to it.

For every fixed positive width and every admissible tail:

* RH is equivalent to pointwise nonnegativity of the explicit prime--Gamma samples on that tail;
* every horizontal zero-free region is equivalent to the corresponding negative-source energy;
* the negative-source Dirichlet abscissa is `-infinity` under RH and is exactly
  `1 + xiRightTransverseSup` under false RH.

Thus the sharp source identity is not merely an evaluation of a divisor-defined observable.  It
gives a source-only coefficient whose sign and Dirichlet spectrum carry the complete transverse
Xi divisor.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

/-- The explicit logarithmic sharp source sample: a finite prime autocorrelation plus the real
part of the completed Gamma contribution. -/
def xiRectangularPrimeGammaLogCoefficient (L : ℝ) (n : ℕ) : ℝ :=
  -2 * rectangularPrimeAutocorrelationSum L (Real.log n / 2) +
    (normalizedRectangularBottomArchContribution L (Real.log n / 2)).re

/-- On every admissible sample, the explicit finite-prime--Gamma coefficient is exactly the real
sharp rectangular Xi-Weil value. -/
theorem xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hLn : L ≤ Real.log n / 2) :
    xiRectangularPrimeGammaLogCoefficient L n =
      (xiRectangularWeilLogCoefficient L n).re := by
  unfold xiRectangularPrimeGammaLogCoefficient xiRectangularWeilLogCoefficient
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, mul_zero, sub_zero] using
    congrArg Complex.re
      (xiWeilPolarization_rectangular_eq_prime_add_arch hL hLn).symm

/-- The explicit source sequence after deleting an arbitrary finite prefix. -/
def xiRectangularPrimeGammaTailCoefficient (L : ℝ) (N n : ℕ) : ℝ :=
  if N ≤ n then xiRectangularPrimeGammaLogCoefficient L n else 0

/-- On an admissible tail, the source sequence is pointwise identical to the real observable
Weil sequence, including the deleted prefix. -/
theorem xiRectangularPrimeGammaTailCoefficient_eq_weilTail_re
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    xiRectangularPrimeGammaTailCoefficient L N =
      fun n => (xiRectangularWeilTailCoefficient L N n).re := by
  funext n
  by_cases hn : N ≤ n
  · rw [xiRectangularPrimeGammaTailCoefficient, if_pos hn,
      xiRectangularWeilTailCoefficient, if_pos hn]
    exact xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re
      hL (hN n hn).2
  · simp [xiRectangularPrimeGammaTailCoefficient,
      xiRectangularWeilTailCoefficient, hn]

/-- The pointwise negative mass of the explicit prime--Gamma source tail. -/
def xiRectangularPrimeGammaTailNegativePart (L : ℝ) (N n : ℕ) : ℝ :=
  (xiRectangularPrimeGammaTailCoefficient L N n)⁻

/-- The source negative mass and the observable Weil negative mass coincide exactly. -/
theorem xiRectangularPrimeGammaTailNegativePart_eq_weilTailNegativePart
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    xiRectangularPrimeGammaTailNegativePart L N =
      xiRectangularWeilTailNegativePart L N := by
  funext n
  rw [xiRectangularPrimeGammaTailNegativePart,
    xiRectangularWeilTailNegativePart,
    congrFun (xiRectangularPrimeGammaTailCoefficient_eq_weilTail_re hL hN) n]

/-- The negative prime--Gamma source mass regarded as a complex Dirichlet coefficient. -/
def xiRectangularPrimeGammaTailNegativeDirichletCoefficient
    (L : ℝ) (N n : ℕ) : ℂ :=
  ((xiRectangularPrimeGammaTailNegativePart L N n : ℝ) : ℂ)

/-- The source-only and observable negative Dirichlet coefficients are pointwise identical. -/
theorem xiRectangularPrimeGammaTailNegativeDirichletCoefficient_eq_weil
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N =
      xiRectangularWeilTailNegativeDirichletCoefficient L N := by
  funext n
  rw [xiRectangularPrimeGammaTailNegativeDirichletCoefficient,
    xiRectangularWeilTailNegativeDirichletCoefficient,
    congrFun
      (xiRectangularPrimeGammaTailNegativePart_eq_weilTailNegativePart hL hN) n]

/-- **Source-only sharp RH criterion.**  For every fixed positive width and every admissible
tail, RH is equivalent to nonnegativity of every finite-prime--Gamma sample on that tail. -/
theorem riemannHypothesis_iff_primeGammaLogCoefficient_tail_nonneg
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      ∀ n : ℕ, N ≤ n → 0 ≤ xiRectangularPrimeGammaLogCoefficient L n := by
  constructor
  · intro hRH n hn
    rw [xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re
      hL.le (hN n hn).2]
    exact (riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL).mp hRH n
  · intro hsource
    apply (riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow hL).mpr
    refine ⟨0, N, fun n hn _hLn => ?_⟩
    change 0 ≤ (xiRectangularWeilLogCoefficient L n).re
    rw [← xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re
      hL.le (hN n hn).2]
    exact hsource n hn

/-- At every transverse width, the horizontal Xi zero-free region is exactly the shifted
Dirichlet-energy law of the explicit prime--Gamma negative mass. -/
theorem xiZeroHalfPlaneBound_iff_primeGammaTailNegativeEnergyAbove
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    XiZeroHalfPlaneBound alpha ↔
      XiRectangularNegativeChannelEnergyAbove alpha
        (xiRectangularPrimeGammaTailNegativePart L N) := by
  rw [xiRectangularPrimeGammaTailNegativePart_eq_weilTailNegativePart hL.le hN]
  exact xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove hL halpha hN

/-- **Prime--Gamma source/divisor/energy spectrum.**  The complete inverse-tilted source, the
intrinsic critical-Mellin defect, and the explicit sharp prime--Gamma negative energy all encode
the same horizontal Xi zero-free half-plane. -/
theorem ccmPrimeGammaSourceDivisorEnergySpectrum_capstone
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    XiZeroHalfPlaneBound alpha ↔
      InverseTiltedDyadicSourceAnalyticAbove alpha ∧
      CriticalMellinDefectAnalyticAbove alpha ∧
      XiRectangularNegativeChannelEnergyAbove alpha
        (xiRectangularPrimeGammaTailNegativePart L N) := by
  rw [xiRectangularPrimeGammaTailNegativePart_eq_weilTailNegativePart hL.le hN]
  exact ccmQuantitativeSourceDivisorEnergySpectrum_capstone hL halpha hN

/-- The endpoint of the explicit prime--Gamma source/divisor/energy spectrum is exactly RH. -/
theorem riemannHypothesis_iff_ccmPrimeGammaSourceDivisorEnergyEndpoint
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      InverseTiltedDyadicSourceAnalyticAbove 0 ∧
      CriticalMellinDefectAnalyticAbove 0 ∧
      XiRectangularNegativeChannelEnergyAbove 0
        (xiRectangularPrimeGammaTailNegativePart L N) := by
  rw [xiRectangularPrimeGammaTailNegativePart_eq_weilTailNegativePart hL.le hN]
  exact riemannHypothesis_iff_ccmSourceDivisorEnergyEndpoint hL hN

/-- Full unconditional abscissa dichotomy for the explicit prime--Gamma negative source. -/
theorem xiRectangularPrimeGammaTailNegativePart_abscissa_dichotomy
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (RiemannHypothesis ∧
        LSeries.abscissaOfAbsConv
          (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) = ⊥) ∨
      (¬ RiemannHypothesis ∧
        LSeries.abscissaOfAbsConv
          (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) =
            ((1 + xiRightTransverseSup : ℝ) : EReal)) := by
  rw [xiRectangularPrimeGammaTailNegativeDirichletCoefficient_eq_weil hL.le hN]
  exact xiRectangularNegativePart_abscissa_dichotomy hL hN

/-- Under RH, the explicit negative-source abscissa is `-infinity`. -/
theorem xiRectangularPrimeGammaTailNegativePart_abscissa_eq_bot_of_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hRH : RiemannHypothesis) :
    LSeries.abscissaOfAbsConv
        (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) = ⊥ := by
  rw [xiRectangularPrimeGammaTailNegativeDirichletCoefficient_eq_weil hL.le hN]
  exact xiRectangularNegativePart_abscissa_eq_bot_of_rh hL N hRH

/-- Under false RH, the explicit negative-source abscissa is exactly the full shifted transverse
Xi displacement. -/
theorem xiRectangularPrimeGammaTailNegativePart_abscissa_eq_transverseSup_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis) :
    LSeries.abscissaOfAbsConv
        (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) =
      ((1 + xiRightTransverseSup : ℝ) : EReal) := by
  rw [xiRectangularPrimeGammaTailNegativeDirichletCoefficient_eq_weil hL.le hN]
  exact xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh hL hN hnot

/-- **Critical abscissa RH criterion.**  RH is equivalent to the explicit prime--Gamma negative
source having absolute-convergence abscissa `-infinity`. -/
theorem riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_eq_bot
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      LSeries.abscissaOfAbsConv
        (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) = ⊥ := by
  constructor
  · exact xiRectangularPrimeGammaTailNegativePart_abscissa_eq_bot_of_rh hL hN
  · intro habs
    by_contra hnot
    have hfinite :=
      xiRectangularPrimeGammaTailNegativePart_abscissa_eq_transverseSup_of_not_rh
        hL hN hnot
    rw [habs] at hfinite
    exact EReal.bot_ne_coe _ hfinite

end

end RHTower
