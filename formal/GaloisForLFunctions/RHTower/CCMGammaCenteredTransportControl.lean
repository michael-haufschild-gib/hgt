import GaloisForLFunctions.RHTower.CCMGammaLogTranslationControl

/-!
# Centered transport retains the translation-increment phase

The centered autocorrelation difference is exactly a signed autocorrelation
of the complete translation increment. Its absolute value costs the full
defect, rather than the square root of that defect times the source norm.
The remaining Gamma energy therefore controls it with a logarithmic modulus,
uniformly in aperture and coefficients. No symmetric pairing of actual prime
cells is assumed or asserted.
-/

open scoped InnerProductSpace
noncomputable section
namespace RHTower

/-- Exact signed centered transport; both copies contain the whole source. -/
theorem ccmActualHeadAutocorrelation_centered_eq_increment_inner
    (s h : ℝ) (f : SoninL2) :
    ccmActualHeadSymmetricAutocorrelation (s + h) f +
        ccmActualHeadSymmetricAutocorrelation (s - h) f -
          2 * ccmActualHeadSymmetricAutocorrelation s f =
      -(inner ℂ (logTranslationCLM s (logTranslationCLM h f - f))
        (logTranslationCLM h f - f)).re := by
  have hshift (v w : ℝ) :
      (inner ℂ (logTranslationCLM v f) (logTranslationCLM w f)).re =
        ccmActualHeadSymmetricAutocorrelation (v - w) f := by
    rw [ccmActualHeadSymmetricAutocorrelation_eq_re_inner]
    have heq : inner ℂ (logTranslationCLM v f) (logTranslationCLM w f) =
        inner ℂ (logTranslationCLM (-w) (logTranslationCLM v f)) f := by
      rw [inner_logTranslationCLM (-w), neg_neg]
    rw [heq, logTranslationCLM_add_apply,
      show -w + v = v - w by ring]
  simp only [map_sub, logTranslationCLM_add_apply, inner_sub_left,
    inner_sub_right, Complex.sub_re]
  rw [hshift, hshift, ← ccmActualHeadSymmetricAutocorrelation_eq_re_inner,
    ← ccmActualHeadSymmetricAutocorrelation_eq_re_inner, add_sub_cancel_right]
  ring

/-- Centered transport costs one complete translation defect, with no source
norm factor and no derivative or degree loss. -/
theorem abs_ccmActualHeadAutocorrelation_centered_le_defect
    (s h : ℝ) (f : SoninL2) :
    |ccmActualHeadSymmetricAutocorrelation (s + h) f +
        ccmActualHeadSymmetricAutocorrelation (s - h) f -
          2 * ccmActualHeadSymmetricAutocorrelation s f| ≤
      ccmActualHeadTranslationDefect h f := by
  rw [ccmActualHeadAutocorrelation_centered_eq_increment_inner, abs_neg]
  calc
    _ ≤ ‖inner ℂ (logTranslationCLM s (logTranslationCLM h f - f))
        (logTranslationCLM h f - f)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖logTranslationCLM s (logTranslationCLM h f - f)‖ *
        ‖logTranslationCLM h f - f‖ := norm_inner_le_norm _ _
    _ = _ := by rw [logTranslation_norm, ccmActualHeadTranslationDefect, pow_two]

/-- The centered transport error has a logarithmic Gamma bound for every
complete form-domain head and every center, including a prime logarithm. -/
theorem ccmActualHeadAutocorrelation_centered_log_bound
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (L : {L : ℝ // 0 < L})
    (h : {h : ℝ // 0 < h ∧ 2 * h < (L : ℝ)}) (s : ℝ) :
    Real.log ((L : ℝ) / (2 * (h : ℝ))) *
        |ccmActualHeadSymmetricAutocorrelation (s + (h : ℝ))
            (ccmArchimedeanFormToAperture a u : SoninL2) +
          ccmActualHeadSymmetricAutocorrelation (s - (h : ℝ))
            (ccmArchimedeanFormToAperture a u : SoninL2) -
          2 * ccmActualHeadSymmetricAutocorrelation s
            (ccmArchimedeanFormToAperture a u : SoninL2)| ≤
      8 * Real.exp (5 * (L : ℝ) / 2) *
        ccmActualHeadGammaHigherBinetModeEnergy
          (ccmArchimedeanFormToAperture a u : SoninL2) := by
  have hlog : 0 ≤ Real.log ((L : ℝ) / (2 * (h : ℝ))) :=
    Real.log_nonneg ((one_le_div (by linarith [h.property.1])).mpr h.property.2.le)
  exact (mul_le_mul_of_nonneg_left
    (abs_ccmActualHeadAutocorrelation_centered_le_defect s h
      (ccmArchimedeanFormToAperture a u : SoninL2)) hlog).trans
        (ccmActualHeadTranslationDefect_log_bound a u L h)

end RHTower
