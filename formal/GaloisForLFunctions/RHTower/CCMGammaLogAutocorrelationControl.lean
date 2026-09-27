import GaloisForLFunctions.RHTower.CCMGammaLogTranslationControl

/-!
# Logarithmic control of complete autocorrelation transport

This controls a displacement from any lag, including an actual prime
logarithm. The source remains whole inside both autocorrelations; no
coefficientwise or primewise diagonal replacement is made.
-/

noncomputable section
namespace RHTower

/-- A coefficient-independent transport estimate for the complete source
autocorrelation, using only the uncancelled higher Gamma energy. -/
theorem ccmActualHeadSymmetricAutocorrelation_sub_log_bound
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (L : {L : ℝ // 0 < L})
    (h : {h : ℝ // 0 < h ∧ 2 * h < (L : ℝ)}) (s : ℝ) :
    Real.log ((L : ℝ) / (2 * (h : ℝ))) *
        (ccmActualHeadSymmetricAutocorrelation (s + (h : ℝ))
            (ccmArchimedeanFormToAperture a u : SoninL2) -
          ccmActualHeadSymmetricAutocorrelation s
            (ccmArchimedeanFormToAperture a u : SoninL2)) ^ 2 ≤
      8 * Real.exp (5 * (L : ℝ) / 2) *
        ‖(ccmArchimedeanFormToAperture a u : SoninL2)‖ ^ 2 *
          ccmActualHeadGammaHigherBinetModeEnergy
            (ccmArchimedeanFormToAperture a u : SoninL2) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  have hE : 0 ≤ ccmActualHeadTranslationDefect h f := by
    unfold ccmActualHeadTranslationDefect
    positivity
  have hlog : 0 ≤ Real.log ((L : ℝ) / (2 * (h : ℝ))) :=
    Real.log_nonneg ((one_le_div (by linarith [h.property.1])).mpr h.property.2.le)
  have hC := abs_ccmActualHeadSymmetricAutocorrelation_sub_le_norm_mul_sqrt_defect
    (s + (h : ℝ)) s f
  rw [add_sub_cancel_left] at hC
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hC 2
  rw [mul_pow, Real.sq_sqrt hE, sq_abs] at hsq
  have hbound := ccmActualHeadTranslationDefect_log_bound a u L h
  change Real.log ((L : ℝ) / (2 * (h : ℝ))) *
      ccmActualHeadTranslationDefect h f ≤
    8 * Real.exp (5 * (L : ℝ) / 2) * ccmActualHeadGammaHigherBinetModeEnergy f at hbound
  have h₁ := mul_le_mul_of_nonneg_left hsq hlog
  have h₂ := mul_le_mul_of_nonneg_left hbound (sq_nonneg ‖f‖)
  change _ ≤ 8 * Real.exp (5 * (L : ℝ) / 2) * ‖f‖ ^ 2 *
    ccmActualHeadGammaHigherBinetModeEnergy f
  nlinarith only [h₁, h₂]

end RHTower
