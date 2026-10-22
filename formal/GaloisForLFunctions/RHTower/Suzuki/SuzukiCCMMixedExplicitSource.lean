import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedSmoothCore
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMSourceFormBridge

/-!
# Explicit mixed Suzuki--CCM source distribution

This module evaluates the exact closed CCM form on arbitrary complex strict-interior smooth
sources in the literal Hermitian correlation coordinate.  Every finite prime-power coefficient
and both polar moments retain the published normalization.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct FourierTransform SchwartzMap BigOperators
noncomputable section
namespace RHTower

theorem ccmComplexSmoothCrossCorrelation_apply
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    ccmComplexSmoothCrossCorrelation u v h =
      ∫ x : ℝ, v x * star (u (x - h)) := by
  rw [ccmComplexSmoothCrossCorrelation,
    SchwartzMap.crossCorrelationSchwartz,
    SchwartzMap.convolution_apply,
    MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards with x
  simp [SchwartzMap.conjugateReflectionSchwartz_apply]

/-- Logarithmic translation is exactly evaluation of the mixed Hermitian correlation at the
opposite lag. -/
theorem inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    inner ℂ
        (logTranslationCLM h
          (ccmArchimedeanFormToAperture a u.toCCMFormVector).1)
        (ccmArchimedeanFormToAperture a v.toCCMFormVector).1 =
      ccmComplexSmoothCrossCorrelation u v (-h) := by
  rw [inner_logTranslationCLM_ccmComplexSmoothFormVector,
    ccmComplexSmoothCrossCorrelation_apply]
  apply integral_congr_ae
  filter_upwards with x
  simp only [sub_neg_eq_add]
  ring

/-- Literal mixed polar--prime distribution in the correlation coordinate. -/
def ccmComplexSmoothPolarPrimeSource
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) : ℂ :=
  star (∫ x : ℝ, (Real.exp ((-1 / 2 : ℝ) * x) : ℂ) * u x) *
      (∫ x : ℝ, (Real.exp ((1 / 2 : ℝ) * x) : ℂ) * v x) +
    star (∫ x : ℝ, (Real.exp ((1 / 2 : ℝ) * x) : ℂ) * u x) *
      (∫ x : ℝ, (Real.exp ((-1 / 2 : ℝ) * x) : ℂ) * v x) -
    ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      (criticalMellinAtomWeight n : ℂ) *
        (ccmComplexSmoothCrossCorrelation u v (Real.log n) +
          ccmComplexSmoothCrossCorrelation u v (-Real.log n))

/-- The literal mixed CCM source form is the polar--prime distribution minus the global
archimedean Weil distribution of the same Hermitian correlation. -/
theorem ccmRestrictedWeilMixedSourceForm_eq_explicitDistribution
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilMixedSourceForm a u.toCCMFormVector v.toCCMFormVector =
      ccmComplexSmoothPolarPrimeSource u v -
        ccmArchimedeanWeilDistribution
          (ccmComplexSmoothCrossCorrelationTest u v) := by
  have hphase :=
    integral_two_gammaHardyPhaseRate_mul_fourier_cross_eq_neg_weilDistribution u v
  have hFourierU := u.toCCMFormVector_fourier_coeFn
  have hFourierV := v.toCCMFormVector_fourier_coeFn
  have hphase' :
      (∫ xi : ℝ,
          ((2 * gammaHardyPhaseRate (2 * Real.pi * xi) : ℝ) : ℂ) *
            star (((u.toCCMFormVector).1 : ℝ → ℂ) xi) *
              ((v.toCCMFormVector).1 : ℝ → ℂ) xi) =
        -ccmArchimedeanWeilDistribution
          (ccmComplexSmoothCrossCorrelationTest u v) := by
    rw [← hphase]
    apply integral_congr_ae
    filter_upwards [hFourierU, hFourierV] with xi hu hv
    rw [hu, hv]
  unfold ccmRestrictedWeilMixedSourceForm
  dsimp only
  rw [hphase']
  simp_rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector]
  simp_rw [inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation]
  have hsum :
      (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (((1 / Real.sqrt n : ℝ) : ℂ) *
            (ccmComplexSmoothCrossCorrelation u v (-Real.log n) +
              ccmComplexSmoothCrossCorrelation u v (-(-Real.log n))))) =
        ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
          (criticalMellinAtomWeight n : ℂ) *
            (ccmComplexSmoothCrossCorrelation u v (Real.log n) +
              ccmComplexSmoothCrossCorrelation u v (-Real.log n)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := by
      have hnmem := Finset.mem_Icc.mp hn
      omega
    rw [criticalMellinAtomWeight_eq_primePairWeight hnpos]
    unfold GaloisForLFunctions.HTGeometry.primePairWeight
    push_cast
    ring
  rw [hsum]
  unfold ccmComplexSmoothPolarPrimeSource
  ring

/-- Closed CCM form, evaluated completely on mixed complex smooth sources. -/
theorem ccmRestrictedWeilForm_ccmComplexSmooth_eq_explicitDistribution
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilForm a u.toCCMFormVector v.toCCMFormVector =
      ccmComplexSmoothPolarPrimeSource u v -
        ccmArchimedeanWeilDistribution
          (ccmComplexSmoothCrossCorrelationTest u v) := by
  rw [ccmRestrictedWeilForm_eq_mixedSource]
  exact ccmRestrictedWeilMixedSourceForm_eq_explicitDistribution u v

end RHTower
