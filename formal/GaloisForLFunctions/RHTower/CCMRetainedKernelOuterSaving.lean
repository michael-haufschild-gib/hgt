import GaloisForLFunctions.RHTower.CCMRetainedKernelLower
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeOuterShell

/-!
# Outer-shell saving for the complete retained kernel

The retained actual frequency weight is real and even, so its physical kernel
is real. Beyond half the aperture diameter, the real autocorrelation costs at
most half the physical norm squared. This gives an exact nonnegative saving
in the signed-kernel bound, uniform over the whole form domain.
-/

open Complex MeasureTheory Set
open scoped FourierTransform InnerProduct
noncomputable section
namespace RHTower

/-- The real autocorrelation is even, with no symmetry assumption on the vector. -/
theorem re_ccmApertureCorrelation_neg (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (h : ℝ) :
    (ccmApertureCorrelation a f (-h)).re = (ccmApertureCorrelation a f h).re := by
  unfold ccmApertureCorrelation
  rw [inner_logTranslationCLM (-h), neg_neg]
  exact inner_re_symm (𝕜 := ℂ) f.1 (logTranslationCLM h f.1)

private theorem abs_re_correlation_pos (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) {h : ℝ} (hh : a.1 < h) :
    |(ccmApertureCorrelation a f h).re| ≤ (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  let S := ccmApertureCompression a (ccmSymmetricLogTranslation h)
  have hn : ‖S f‖ ≤ ‖f‖ := calc
    _ ≤ ‖S‖ * ‖f‖ := S.le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (norm_ccmApertureSymmetricTranslation_le_one a hh) (norm_nonneg _)
    _ = _ := one_mul _
  have he : (inner ℂ (S f) f).re = 2 * (ccmApertureCorrelation a f h).re := by
    rw [inner_ccmApertureCompression]
    change (inner ℂ (logTranslationCLM h f.1 + logTranslationCLM (-h) f.1) f.1).re = _
    rw [inner_add_left, Complex.add_re]
    change (ccmApertureCorrelation a f h).re + (ccmApertureCorrelation a f (-h)).re = _
    rw [re_ccmApertureCorrelation_neg]
    ring
  have hb : |(inner ℂ (S f) f).re| ≤ ‖f‖ ^ 2 := calc
    _ ≤ ‖inner ℂ (S f) f‖ := Complex.abs_re_le_norm _
    _ ≤ ‖S f‖ * ‖f‖ := norm_inner_le_norm (𝕜 := ℂ) (S f) f
    _ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = _ := (pow_two _).symm
  rw [he, abs_mul, abs_of_pos zero_lt_two] at hb
  linarith

/-- Outer translations have half the real correlation budget on every aperture vector. -/
theorem abs_re_ccmApertureCorrelation_le_half (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) {h : ℝ} (hh : a.1 < |h|) :
    |(ccmApertureCorrelation a f h).re| ≤ (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  by_cases hp : 0 ≤ h
  · exact abs_re_correlation_pos a f (by simpa only [abs_of_nonneg hp] using hh)
  · have hm : a.1 < -h := by simpa only [abs_of_neg (lt_of_not_ge hp)] using hh
    simpa only [re_ccmApertureCorrelation_neg] using abs_re_correlation_pos a f hm

theorem ccmRetainedSignedFrequencyWeight_even (a : SuzukiPositiveAperture)
    (α R θ ξ : ℝ) :
    ccmRetainedSignedFrequencyWeight a α R θ (-ξ) =
      ccmRetainedSignedFrequencyWeight a α R θ ξ := by
  simp only [ccmRetainedSignedFrequencyWeight, ccmActualSourceNegativeWeight,
    ccmPositiveFrequencyWeight, ccmActualWeilSymbol, mul_neg,
    correctedCCMSymbol_even, ccmFrequencyTent, abs_neg]

private theorem fourier_real_even (w : ℝ → ℝ) (he : ∀ x, w (-x) = w x) (h : ℝ) :
    𝓕 (fun x => (w x : ℂ)) h = star (𝓕 (fun x => (w x : ℂ)) h) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj, ← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, map_mul, he, Complex.conj_ofReal]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Actual signed kernel is real; neither the source nor its coefficients need be real. -/
theorem ccmRetainedPhysicalKernel_im (a : SuzukiPositiveAperture)
    (α R θ h : ℝ) : (ccmRetainedPhysicalKernel a α R θ h).im = 0 := by
  have he := fourier_real_even (ccmRetainedSignedFrequencyWeight a α R θ)
    (ccmRetainedSignedFrequencyWeight_even a α R θ) (-h)
  rw [← Real.fourierInv_eq_fourier_neg] at he
  have hi := congrArg Complex.im he
  change (ccmRetainedPhysicalKernel a α R θ h).im =
    -(ccmRetainedPhysicalKernel a α R θ h).im at hi
  linarith

theorem continuous_ccmRetainedPhysicalKernel (a : SuzukiPositiveAperture)
    (α R θ : ℝ) : Continuous (ccmRetainedPhysicalKernel a α R θ) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂.neg (integrable_ccmRetainedSignedFrequencyWeight a α R θ)

/-- Exact saving from the outer translation shell. -/
def ccmRetainedKernelOuterSaving (a : SuzukiPositiveAperture) (α R θ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ h in Icc (-2*a.1) (2*a.1) \ Icc (-a.1) a.1,
    ‖ccmRetainedPhysicalKernel a α R θ h‖

def ccmRetainedKernelShellCeiling (a : SuzukiPositiveAperture) (α R θ : ℝ) : ℝ :=
  (∫ h in Icc (-a.1) a.1, ‖ccmRetainedPhysicalKernel a α R θ h‖) +
    ccmRetainedKernelOuterSaving a α R θ

theorem ccmRetainedKernelOuterSaving_nonneg (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    0 ≤ ccmRetainedKernelOuterSaving a α R θ := by
  unfold ccmRetainedKernelOuterSaving
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)

theorem ccmRetainedKernelShellCeiling_nonneg (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    0 ≤ ccmRetainedKernelShellCeiling a α R θ :=
  add_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (ccmRetainedKernelOuterSaving_nonneg a α R θ)

private theorem inner_interval_subset (a : SuzukiPositiveAperture) :
    Icc (-a.1) a.1 ⊆ Icc (-2*a.1) (2*a.1) := by
  intro x hx
  constructor <;> linarith [hx.1, hx.2, a.property]

/-- The new ceiling plus the explicit saving recovers the unsplit kernel ceiling exactly. -/
theorem ccmRetainedKernelShellCeiling_add_saving (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    ccmRetainedKernelShellCeiling a α R θ + ccmRetainedKernelOuterSaving a α R θ =
      ccmRetainedKernelCeiling a α R θ := by
  unfold ccmRetainedKernelShellCeiling ccmRetainedKernelOuterSaving
  rw [setIntegral_sdiff measurableSet_Icc
    (continuous_ccmRetainedPhysicalKernel a α R θ).norm.integrableOn_Icc
    (inner_interval_subset a)]
  change _ = ∫ h in Icc (-2*a.1) (2*a.1), ‖ccmRetainedPhysicalKernel a α R θ h‖
  ring

theorem ccmRetainedKernelShellCeiling_le (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    ccmRetainedKernelShellCeiling a α R θ ≤ ccmRetainedKernelCeiling a α R θ := by
  linarith [ccmRetainedKernelShellCeiling_add_saving a α R θ,
    ccmRetainedKernelOuterSaving_nonneg a α R θ]

private theorem shell_pairing_bound (a : SuzukiPositiveAperture) (α R θ : ℝ)
    (f : suzukiApertureHilbert a) :
    |(∫ h, ccmRetainedPhysicalKernel a α R θ h * ccmApertureCorrelation a f h).re| ≤
      ccmRetainedKernelShellCeiling a α R θ * ‖f‖ ^ 2 := by
  let k := ccmRetainedPhysicalKernel a α R θ
  let C := ccmApertureCorrelation a f
  let g : ℝ → ℝ := fun h => (k h).re * (C h).re
  have hk : Continuous k := continuous_ccmRetainedPhysicalKernel a α R θ
  have hc : Continuous C := continuous_ccmApertureCorrelation a f
  have hg : Continuous g := (Complex.continuous_re.comp hk).mul (Complex.continuous_re.comp hc)
  have hkC : Integrable (fun h => k h * C h) :=
    (hk.mul hc).integrable_of_hasCompactSupport
      (hasCompactSupport_ccmApertureCorrelation a f).mul_left
  have he : (∫ h, k h * C h).re = ∫ h, g h := by
    change RCLike.re (∫ h, k h * C h) = ∫ h, g h
    rw [← integral_re hkC]
    apply integral_congr_ae
    filter_upwards with h
    change (k h * C h).re = (k h).re * (C h).re
    rw [Complex.mul_re, ccmRetainedPhysicalKernel_im, zero_mul, sub_zero]
  rw [he]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc (-2*a.1) (2*a.1)) (fun h hh => by
      change (k h).re * (ccmApertureCorrelation a f h).re = 0
      rw [ccmApertureCorrelation_eq_zero_of_outside a f hh, Complex.zero_re, mul_zero])]
  have hb (s : Set ℝ) (hs : MeasurableSet s) (hsub : s ⊆ Icc (-2*a.1) (2*a.1))
      (b : ℝ) (hbound : ∀ h ∈ s, |(C h).re| ≤ b * ‖f‖ ^ 2) :
      |∫ h in s, g h| ≤ (∫ h in s, ‖k h‖) * (b * ‖f‖ ^ 2) := by
    calc
      _ ≤ ∫ h in s, |g h| := abs_integral_le_integral_abs
      _ ≤ ∫ h in s, ‖k h‖ * (b * ‖f‖ ^ 2) := by
        apply setIntegral_mono_on (hg.abs.integrableOn_Icc.mono_set hsub)
          ((hk.norm.mul continuous_const).integrableOn_Icc.mono_set hsub) hs
        intro h hh
        change |(k h).re * (C h).re| ≤ _
        rw [abs_mul]
        exact mul_le_mul (Complex.abs_re_le_norm _) (hbound h hh)
          (abs_nonneg _) (norm_nonneg _)
      _ = _ := integral_mul_const _ _
  have hi := hb (Icc (-a.1) a.1) measurableSet_Icc (inner_interval_subset a) 1
    (fun h _ => by simpa only [one_mul] using
      (Complex.abs_re_le_norm (C h)).trans (norm_ccmApertureCorrelation_le a f h))
  have ho := hb (Icc (-2*a.1) (2*a.1) \ Icc (-a.1) a.1)
    (measurableSet_Icc.diff measurableSet_Icc) sdiff_subset (1/2) (fun h hh => by
      apply abs_re_ccmApertureCorrelation_le_half
      exact lt_of_not_ge fun hn => hh.2 (abs_le.mp hn))
  have hsplit := setIntegral_sdiff (μ := (volume : Measure ℝ))
    measurableSet_Icc hg.integrableOn_Icc
    (inner_interval_subset a)
  have hdecomp : (∫ h in Icc (-2*a.1) (2*a.1), g h) =
      (∫ h in Icc (-a.1) a.1, g h) +
      ∫ h in Icc (-2*a.1) (2*a.1) \ Icc (-a.1) a.1, g h := by
    linarith only [hsplit]
  rw [hdecomp]
  calc
    _ ≤ |∫ h in Icc (-a.1) a.1, g h| +
        |∫ h in Icc (-2*a.1) (2*a.1) \ Icc (-a.1) a.1, g h| := abs_add_le _ _
    _ ≤ _ := by
      dsimp only [ccmRetainedKernelShellCeiling, ccmRetainedKernelOuterSaving]
      nlinarith only [hi, ho]

/-- Independent signed-kernel bound with the exact outer-shell saving. -/
theorem ccmRetained_debt_abs_le_kernelShell (a : SuzukiPositiveAperture) (α R θ : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    |(∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmActualSourceNegativeMeasure a α) -
      θ * (∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmPositiveFrequencyMeasure a α R)| ≤
        ccmRetainedKernelShellCeiling a α R θ * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  have he := integral_weight_mul_ccmApertureFourierDensity a
    (ccmArchimedeanFormToAperture a u)
    (fun ξ => (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ))
    (integrable_ccmRetainedSignedFrequencyWeight a α R θ)
  rw [ccmRetainedSignedFrequency_pairing] at he
  have hb := shell_pairing_bound a α R θ (ccmArchimedeanFormToAperture a u)
  change |(∫ h, 𝓕⁻ (fun ξ => (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ)) h *
    ccmApertureCorrelation a (ccmArchimedeanFormToAperture a u) h).re| ≤ _ at hb
  rw [← he, Complex.ofReal_re] at hb
  exact hb

/-- Full form-domain source bound with a kernel budget no larger than before. -/
theorem ccmRestrictedWeilSource_ge_retainedKernelShell (a : SuzukiPositiveAperture)
    (α R : ℝ) (θ : Icc (0 : ℝ) 1) (u : CCMArchimedeanFormDomain a) :
    (α - ccmRetainedKernelShellCeiling a α R θ.1) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  have hsource := ccmRestrictedWeilSource_ge_retainedPositiveWindow a α R θ u
  have hdebt := (le_abs_self _).trans (ccmRetained_debt_abs_le_kernelShell a α R θ.1 u)
  nlinarith only [hsource, hdebt]

end RHTower
