import GaloisForLFunctions.RHTower.PoleVanishingWeilTraceCertificate
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCCMScalingBridge
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilActualHeadCompletedErrorProducer

/-!
# Signed Fourier weights paired with the complete aperture correlation

The physical correlation has compact support even for arbitrary form-domain
sources. Fourier duality therefore bounds a signed spectral pairing by the
integral of its physical kernel over the aperture diameter. The signed weight
is assembled before taking any modulus; no coefficient or matrix-order count
enters the bound.
-/

open Complex MeasureTheory Set
open scoped InnerProduct FourierTransform
noncomputable section
namespace RHTower

def ccmApertureCorrelation (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (h : ℝ) : ℂ :=
  inner ℂ (logTranslationCLM h f.1) f.1

theorem continuous_ccmApertureCorrelation (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : Continuous (ccmApertureCorrelation a f) :=
  (continuous_logTranslationCLM f.1).inner continuous_const

theorem norm_ccmApertureCorrelation_le (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (h : ℝ) :
    ‖ccmApertureCorrelation a f h‖ ≤ ‖f‖ ^ 2 := by
  have hn : ‖logTranslationCLM h f.1‖ = ‖f.1‖ :=
    (MellinL2.additiveTranslationUnitary h).norm_map f.1
  simpa only [ccmApertureCorrelation, hn, pow_two, Submodule.norm_coe] using
    norm_inner_le_norm (𝕜 := ℂ) (logTranslationCLM h f.1) f.1

theorem ccmApertureCorrelation_eq_zero_of_outside (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) {h : ℝ} (hh : h ∉ Icc (-2*a.1) (2*a.1)) :
    ccmApertureCorrelation a f h = 0 := by
  by_cases hp : 2*a.1 < h
  · exact inner_logTranslationCLM_eq_zero_of_aperture a f hp
  · have hm : 2*a.1 < -h := by
      simp only [mem_Icc, not_and_or, not_le] at hh
      rcases hh with hh | hh <;> linarith
    have hz := inner_logTranslationCLM_eq_zero_of_aperture a f hm
    rw [inner_logTranslationCLM (-h), neg_neg, ← inner_conj_symm] at hz
    exact star_eq_zero.mp hz

theorem hasCompactSupport_ccmApertureCorrelation (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : HasCompactSupport (ccmApertureCorrelation a f) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro h hh
  exact ccmApertureCorrelation_eq_zero_of_outside a f hh

theorem integrable_ccmApertureCorrelation (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : Integrable (ccmApertureCorrelation a f) :=
  (continuous_ccmApertureCorrelation a f).integrable_of_hasCompactSupport
    (hasCompactSupport_ccmApertureCorrelation a f)

def ccmApertureFourierDensity (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (ξ : ℝ) : ℂ :=
  ((‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ)

theorem continuous_ccmApertureFourierDensity (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : Continuous (ccmApertureFourierDensity a f) := by
  have h : Continuous (𝓕 (f.1 : ℝ → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_suzukiApertureHilbert a f)
  exact Complex.continuous_ofReal.comp (h.norm.pow 2)

theorem integrable_ccmApertureFourierDensity (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : Integrable (ccmApertureFourierDensity a f) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (fourierUnitary f.1) (fourierUnitary f.1)
  apply h.congr
  filter_upwards [fourierUnitary_ae_eq_fourier_of_integrable f.1
    (integrable_suzukiApertureHilbert a f)] with ξ hξ
  rw [hξ, inner_self_eq_norm_sq_to_K]
  simp only [ccmApertureFourierDensity, Complex.ofReal_pow]
  rfl

/-- Full complex Fourier/correlation identity, without evenness of the source. -/
theorem fourier_ccmApertureFourierDensity (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    𝓕 (ccmApertureFourierDensity a f) = ccmApertureCorrelation a f := by
  funext h
  have he := inner_logTranslation_fourierUnitary_symm h (fourierUnitary f.1)
  rw [fourierUnitary.symm_apply_apply] at he
  rw [ccmApertureCorrelation, he, MeasureTheory.L2.inner_def, Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [MellinL2.fourierPhaseMulAux_ae h (fourierUnitary f.1),
    fourierUnitary_ae_eq_fourier_of_integrable f.1
      (integrable_suzukiApertureHilbert a f)] with ξ hp hξ
  change (Real.fourierChar (-(ξ*h))) • ccmApertureFourierDensity a f ξ =
    inner ℂ (MellinL2.fourierPhaseMulAux h (fourierUnitary f.1) ξ) (fourierUnitary f.1 ξ)
  rw [hp, hξ]
  simp only [ccmApertureFourierDensity, Circle.smul_def, smul_eq_mul,
    RCLike.inner_apply', map_mul, starRingEnd_apply, MellinL2.fourierPhase]
  rw [AddChar.map_neg_eq_inv]
  rw [Circle.coe_inv_eq_conj, mul_comm ξ h]
  change star (Real.fourierChar (h * ξ) : ℂ) *
    ((‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) =
    star (Real.fourierChar (h * ξ) : ℂ) * star (𝓕 (f.1 : ℝ → ℂ) ξ) *
      𝓕 (f.1 : ℝ → ℂ) ξ
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [starRingEnd_apply, mul_assoc]

/-- Exact dual pairing: frequency cancellation becomes physical kernel cancellation. -/
theorem integral_weight_mul_ccmApertureFourierDensity
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (w : ℝ → ℂ) (hw : Integrable w) :
    (∫ ξ, w ξ * ccmApertureFourierDensity a f ξ) =
      ∫ h, 𝓕⁻ w h * ccmApertureCorrelation a f h := by
  have hi := (continuous_ccmApertureFourierDensity a f).fourierInv_fourier_eq
    (integrable_ccmApertureFourierDensity a f)
    (by rw [fourier_ccmApertureFourierDensity]; exact integrable_ccmApertureCorrelation a f)
  rw [fourier_ccmApertureFourierDensity] at hi
  have hd := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := -(innerₗ ℝ)) Real.continuous_fourierChar continuous_inner.neg hw
    (integrable_ccmApertureCorrelation a f)
  have hflip : (-(innerₗ ℝ)).flip = -(innerₗ ℝ) := by ext; rfl
  rw [hflip] at hd
  change (∫ h, 𝓕⁻ w h * ccmApertureCorrelation a f h) =
    ∫ ξ, w ξ * 𝓕⁻ (ccmApertureCorrelation a f) ξ at hd
  rw [hi] at hd
  exact hd.symm

def ccmApertureSignedKernelMass (a : SuzukiPositiveAperture) (w : ℝ → ℂ) : ℝ :=
  ∫ h in Icc (-2*a.1) (2*a.1), ‖𝓕⁻ w h‖

theorem ccmApertureSignedKernelMass_nonneg (a : SuzukiPositiveAperture) (w : ℝ → ℂ) :
    0 ≤ ccmApertureSignedKernelMass a w := integral_nonneg fun _ => norm_nonneg _

/-- A coefficient-uniform bound on the whole aperture, with the signed kernel retained intact. -/
theorem norm_integral_weight_mul_ccmApertureFourierDensity_le
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (w : ℝ → ℂ) (hw : Integrable w) :
    ‖∫ ξ, w ξ * ccmApertureFourierDensity a f ξ‖ ≤
      ccmApertureSignedKernelMass a w * ‖f‖ ^ 2 := by
  have hk : Continuous (𝓕⁻ w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg hw
  have hc := continuous_ccmApertureCorrelation a f
  rw [integral_weight_mul_ccmApertureFourierDensity a f w hw]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc (-2*a.1) (2*a.1)) (fun h hh => by
      rw [ccmApertureCorrelation_eq_zero_of_outside a f hh, mul_zero])]
  calc
    _ ≤ ∫ h in Icc (-2*a.1) (2*a.1), ‖𝓕⁻ w h * ccmApertureCorrelation a f h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Icc (-2*a.1) (2*a.1), ‖𝓕⁻ w h‖ * ‖f‖ ^ 2 := by
      apply integral_mono ((hk.mul hc).norm.integrableOn_Icc)
        ((hk.norm.mul continuous_const).integrableOn_Icc)
      intro h
      change ‖𝓕⁻ w h * ccmApertureCorrelation a f h‖ ≤ ‖𝓕⁻ w h‖ * ‖f‖ ^ 2
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_ccmApertureCorrelation_le a f h) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; rfl

end RHTower
