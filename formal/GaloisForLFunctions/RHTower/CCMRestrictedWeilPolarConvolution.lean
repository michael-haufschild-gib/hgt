import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeOuterShell
import GaloisForLFunctions.RHTower.CCMPolarPrimeSourceSign
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier

/-!
# The actual crossed polar term as compressed convolution

The complete difference-interval exponential kernel acts on arbitrary
aperture L2 vectors as exactly the crossed rank-two polar operator. Its
full-line Fourier transform is the corrected polar symbol with the exact
frequency conversion. The global convolution norm pays the high-frequency
source tail in the proposed bounded-remainder iteration argument.
-/

open MeasureTheory Set Filter
open scoped FourierTransform InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The full-line polar convolution profile, with its literal difference aperture. -/
def ccmPolarConvolutionProfile (a : SuzukiPositiveAperture) : ℝ → ℂ :=
  (centralInterval (2 * a.1)).indicator
    (fun h => ccmPolarProfile (1 / 2) h + ccmPolarProfile (-1 / 2) h)

theorem measurable_ccmPolarConvolutionProfile (a : SuzukiPositiveAperture) :
    Measurable (ccmPolarConvolutionProfile a) := by
  have hc : Continuous (fun h : ℝ => ccmPolarProfile (1 / 2) h + ccmPolarProfile (-1 / 2) h) := by
    unfold ccmPolarProfile
    fun_prop
  exact hc.measurable.indicator (measurableSet_centralInterval _)

theorem integrable_ccmPolarConvolutionProfile (a : SuzukiPositiveAperture) :
    Integrable (ccmPolarConvolutionProfile a) := by
  have hc : Continuous (fun h : ℝ => ccmPolarProfile (1 / 2) h + ccmPolarProfile (-1 / 2) h) := by
    unfold ccmPolarProfile
    fun_prop
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

private theorem polar_profile_sub (s x y : ℝ) :
    ccmPolarProfile s (x - y) = ccmPolarProfile s x * ccmPolarProfile (-s) y := by
  unfold ccmPolarProfile
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem ccmPolarConvolutionProfile_sub (a : SuzukiPositiveAperture) {x y : ℝ}
    (hx : x ∈ centralInterval a.1) (hy : y ∈ centralInterval a.1) :
    ccmPolarConvolutionProfile a (x - y) =
      ccmPolarProfile (1 / 2) x * ccmPolarProfile (-1 / 2) y +
      ccmPolarProfile (-1 / 2) x * ccmPolarProfile (1 / 2) y := by
  have hxy : x - y ∈ centralInterval (2 * a.1) := by
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    constructor <;> linarith
  rw [ccmPolarConvolutionProfile, indicator_of_mem hxy,
    polar_profile_sub, polar_profile_sub]
  congr 2 <;> congr 1 <;> ring

/-- The Schur realization of the uncompressed polar convolution. -/
def ccmPolarConvolution (a : SuzukiPositiveAperture) : SoninL2 →L[ℂ] SoninL2 :=
  (convolutionKernel (ccmPolarConvolutionProfile a)
    (measurable_ccmPolarConvolutionProfile a) (integrable_ccmPolarConvolutionProfile a)).op

private theorem aperture_coeFn_support (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    ∀ᵐ y : ℝ, y ∉ centralInterval a.1 → f.1 y = 0 := by
  have h := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert a f] at h
  filter_upwards [h] with y hy
  intro hyI
  rw [hy, indicator_of_notMem hyI]

private theorem polar_convolution_integral (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) {x : ℝ} (hx : x ∈ centralInterval a.1) :
    (∫ y, ccmPolarConvolutionProfile a (x - y) * f.1 y) =
      inner ℂ (ccmPolarApertureVector a (-1 / 2)) f * ccmPolarProfile (1 / 2) x +
      inner ℂ (ccmPolarApertureVector a (1 / 2)) f * ccmPolarProfile (-1 / 2) x := by
  have heq : (fun y => ccmPolarConvolutionProfile a (x - y) * f.1 y) =ᵐ[volume]
      (fun y => ccmPolarProfile (1 / 2) x * inner ℂ (ccmPolarL2Vector a (-1 / 2) y) (f.1 y) +
        ccmPolarProfile (-1 / 2) x * inner ℂ (ccmPolarL2Vector a (1 / 2) y) (f.1 y)) := by
    filter_upwards [ccmPolarL2Vector_coeFn a (-1 / 2), ccmPolarL2Vector_coeFn a (1 / 2),
      aperture_coeFn_support a f] with y hm hp hf
    rw [hm, hp]
    by_cases hy : y ∈ centralInterval a.1
    · rw [ccmPolarConvolutionProfile_sub a hx hy, indicator_of_mem hy, indicator_of_mem hy]
      simp only [ccmPolarProfile, RCLike.inner_apply, Complex.conj_ofReal]
      ring
    · rw [hf hy, mul_zero, inner_zero_right, inner_zero_right]
      simp
  rw [integral_congr_ae heq, integral_add
    ((L2.integrable_inner (ccmPolarL2Vector a (-1 / 2)) f.1).const_mul _)
    ((L2.integrable_inner (ccmPolarL2Vector a (1 / 2)) f.1).const_mul _),
    integral_const_mul, integral_const_mul, ← L2.inner_def, ← L2.inner_def]
  change _ = inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 * ccmPolarProfile (1 / 2) x +
    inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 * ccmPolarProfile (-1 / 2) x
  ring

/-- The actual crossed rank-two pole term is exactly compressed convolution.
The doubled difference aperture is retained, including its endpoints. -/
theorem ccmPolarOperator_eq_compressed_convolution (a : SuzukiPositiveAperture) :
    ccmPolarOperator a = ccmApertureCompression a (ccmPolarConvolution a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  have hval : (ccmPolarOperator a f : SoninL2) =
      inner ℂ (ccmPolarApertureVector a (-1 / 2)) f • ccmPolarL2Vector a (1 / 2) +
      inner ℂ (ccmPolarApertureVector a (1 / 2)) f • ccmPolarL2Vector a (-1 / 2) := by
    simp only [ccmPolarOperator, add_apply, InnerProductSpace.rankOne_apply]
    rfl
  rw [hval, ccmApertureCompression_val]
  apply Lp.ext
  let cp := inner ℂ (ccmPolarApertureVector a (-1 / 2)) f
  let cm := inner ℂ (ccmPolarApertureVector a (1 / 2)) f
  have hc := (convolutionKernel (ccmPolarConvolutionProfile a)
    (measurable_ccmPolarConvolutionProfile a) (integrable_ccmPolarConvolutionProfile a)).op_coeFn f.1
  filter_upwards [Lp.coeFn_add (cp • ccmPolarL2Vector a (1 / 2)) (cm • ccmPolarL2Vector a (-1 / 2)),
    Lp.coeFn_smul cp (ccmPolarL2Vector a (1 / 2)), Lp.coeFn_smul cm (ccmPolarL2Vector a (-1 / 2)),
    ccmPolarL2Vector_coeFn a (1 / 2), ccmPolarL2Vector_coeFn a (-1 / 2),
    indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
      (ccmPolarConvolution a f.1), hc] with x ha hp hm hpp hmm hcut hconv
  rw [ha, Pi.add_apply, hp, hm, Pi.smul_apply, Pi.smul_apply, hpp, hmm, hcut]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
    change (ccmPolarConvolution a f.1) x = ∫ y, ccmPolarConvolutionProfile a (x - y) * f.1 y at hconv
    rw [hconv, polar_convolution_integral a f hx]
    rfl
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx]
    simp

/-- The exponential kernel is the full symmetric polar density. -/
theorem ccmPolarConvolutionProfile_eq_cosh (a : SuzukiPositiveAperture) :
    ccmPolarConvolutionProfile a = (centralInterval (2 * a.1)).indicator
      (fun h : ℝ => ((2 * Real.cosh (h / 2) : ℝ) : ℂ)) := by
  funext h
  by_cases hh : h ∈ centralInterval (2 * a.1)
  · rw [ccmPolarConvolutionProfile, indicator_of_mem hh, indicator_of_mem hh]
    simp only [ccmPolarProfile, show (1 / 2 : ℝ) * h = h / 2 by ring,
      show (-1 / 2 : ℝ) * h = -(h / 2) by ring, Real.cosh_eq]
    push_cast
    ring
  · rw [ccmPolarConvolutionProfile, indicator_of_notMem hh, indicator_of_notMem hh]

/-- The literal full-line polar profile has the corpus's corrected polar
symbol, with the exact Fourier frequency conversion. -/
theorem fourier_ccmPolarConvolutionProfile (a : SuzukiPositiveAperture) (ξ : ℝ) :
    𝓕 (ccmPolarConvolutionProfile a) ξ = (polarMultiplier a.1 (-2 * Real.pi * ξ) : ℂ) := by
  let t := -2 * Real.pi * ξ
  have he (h : ℝ) : (((-2 * Real.pi * h * ξ : ℝ) : ℂ) * Complex.I) =
      (((t * h : ℝ) : ℂ) * Complex.I) := by
    dsimp [t]
    push_cast
    ring
  calc
    _ = ∫ h : ℝ, (centralInterval (2 * a.1)).indicator
        (fun h => ((2 * Real.cosh (h / 2) : ℝ) : ℂ) *
          Complex.exp (((t * h : ℝ) : ℂ) * Complex.I)) h := by
      rw [Real.fourier_real_eq_integral_exp_smul, ccmPolarConvolutionProfile_eq_cosh]
      apply integral_congr_ae
      filter_upwards with h
      by_cases hh : h ∈ centralInterval (2 * a.1)
      · rw [indicator_of_mem hh, indicator_of_mem hh, smul_eq_mul, he, mul_comm]
      · rw [indicator_of_notMem hh, indicator_of_notMem hh, smul_zero]
    _ = polarFourierTransform a.1 t := by
      rw [integral_indicator (measurableSet_centralInterval _)]
      change (∫ h in Icc (-(2 * a.1)) (2 * a.1), _) = _
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show -(2 * a.1) ≤ 2 * a.1 by linarith [a.2])]
      simp only [polarFourierTransform, Complex.ofReal_mul, Complex.ofReal_ofNat]
    _ = _ := polarFourierTransform_eq_polarMultiplier a.2.le

/-- The actual pole operator is the aperture compression of its full Fourier
multiplier; all bound and measurability witnesses are supplied unconditionally. -/
theorem ccmPolarOperator_eq_compressed_fourierMultiplier (a : SuzukiPositiveAperture) :
    ccmPolarOperator a = ccmApertureCompression a
      (fourierMulCLM
        (continuous_fourier_of_integrable' (integrable_ccmPolarConvolutionProfile a)).measurable
        (integral_nonneg fun x => norm_nonneg (ccmPolarConvolutionProfile a x))
        (norm_fourier_apply_le_integral_norm (ccmPolarConvolutionProfile a))) := by
  rw [ccmPolarOperator_eq_compressed_convolution]
  congr 1
  exact convolutionKernel_op_eq_fourierMulCLM _ _ _

/-- The full polar convolution profile has its exact positive mass. -/
theorem integral_norm_ccmPolarConvolutionProfile (a : SuzukiPositiveAperture) :
    (∫ h, ‖ccmPolarConvolutionProfile a h‖) = 8 * Real.sinh a.1 := by
  have hp (h : ℝ) : ‖ccmPolarConvolutionProfile a h‖ =
      (ccmPolarConvolutionProfile a h).re := by
    rw [ccmPolarConvolutionProfile_eq_cosh]
    by_cases hh : h ∈ centralInterval (2 * a.1)
    · rw [indicator_of_mem hh, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
      exact abs_of_nonneg (by positivity)
    · rw [indicator_of_notMem hh]
      simp
  have hzero : (∫ h, ccmPolarConvolutionProfile a h) = ((8 * Real.sinh a.1 : ℝ) : ℂ) := by
    have h := fourier_ccmPolarConvolutionProfile a 0
    simpa only [Real.fourier_real_eq_integral_exp_smul, mul_zero, zero_mul, Complex.ofReal_zero,
      Complex.exp_zero, one_smul, polarMultiplier_zero] using h
  simp_rw [hp]
  have hr := integral_re (𝕜 := ℂ) (integrable_ccmPolarConvolutionProfile a)
  change (∫ h, (ccmPolarConvolutionProfile a h).re) =
    (∫ h, ccmPolarConvolutionProfile a h).re at hr
  rw [hr, hzero, Complex.ofReal_re]

/-- The uncompressed polar term has the global norm bound needed to pay the
high-frequency source tail. -/
theorem norm_ccmPolarConvolution_le (a : SuzukiPositiveAperture) :
    ‖ccmPolarConvolution a‖ ≤ 4 * Real.exp a.1 := by
  have h := norm_fourierMulCLM_le
    (continuous_fourier_of_integrable' (integrable_ccmPolarConvolutionProfile a)).measurable
    (integral_nonneg fun h => norm_nonneg (ccmPolarConvolutionProfile a h))
    (norm_fourier_apply_le_integral_norm (ccmPolarConvolutionProfile a))
  change ‖(convolutionKernel (ccmPolarConvolutionProfile a)
    (measurable_ccmPolarConvolutionProfile a) (integrable_ccmPolarConvolutionProfile a)).op‖ ≤ _
  rw [convolutionKernel_op_eq_fourierMulCLM]
  refine h.trans ?_
  rw [integral_norm_ccmPolarConvolutionProfile, Real.sinh_eq]
  linarith [Real.exp_pos (-a.1)]

end RHTower
end
