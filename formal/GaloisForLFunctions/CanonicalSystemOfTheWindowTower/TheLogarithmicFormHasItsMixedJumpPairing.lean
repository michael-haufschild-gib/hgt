import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.BoundedLipschitzCutoffsPreserveLogarithmicEnergy

/-!
# The complete mixed logarithmic jump form

Polarization identifies the full logarithmic Fourier form with mass plus its
literal translation-loss pairing. Translation preserves both domain and form.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform ENNReal InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

/-- The logarithmic Fourier form in whole-line physical coordinates. -/
def logarithmicFullForm (u v : RealLineL2) : ℂ :=
  ∫ ξ : ℝ, (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
    star (fourierUnitary u ξ) * fourierUnitary v ξ

theorem logarithmicFullForm_halfLine (u v : LogarithmicHalfLineL2) :
    logarithmicFullForm u v = logarithmicHalfLineForm u v := rfl

/-- Finite logarithmic energy makes every mixed logarithmic form integral absolutely convergent. -/
theorem integrable_logarithmicFullForm {u v : RealLineL2}
    (hu : HasLogarithmicEnergy (u : RealLineL2)) (hv : HasLogarithmicEnergy (v : RealLineL2)) :
    Integrable (fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
      star (((Lp.fourierTransformₗᵢ ℝ ℂ (u : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) *
        ((Lp.fourierTransformₗᵢ ℝ ℂ (v : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (hu.toLp _) (hv.toLp _)
  apply hi.congr
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with ξ huξ hvξ
  rw [huξ, hvξ]
  let m := continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)
  have hmod : star m * m = (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) := by
    rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact congrArg Complex.ofReal (continuedLogReferenceFactor_imaginary_norm_sq _)
  simp only [RCLike.inner_apply', starRingEnd_apply, star_mul]
  calc
    _ = (star m * m) *
        star (((Lp.fourierTransformₗᵢ ℝ ℂ (u : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) *
          ((Lp.fourierTransformₗᵢ ℝ ℂ (v : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ := by ring
    _ = _ := by rw [hmod]

/-- Causal coordinates identify the literal logarithmic form with the ordinary L² inner product. -/
theorem logarithmicFullForm_convolution (f g : RealLineL2) :
    logarithmicFullForm (logarithmicConvolution f) (logarithmicConvolution g) = inner ℂ f g := by
  have he : (fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
      star (((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution f) : RealLineL2) : ℝ → ℂ) ξ) *
        ((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution g) : RealLineL2) : ℝ → ℂ) ξ) =ᵐ[volume]
      fun ξ => inner ℂ
        (((Lp.fourierTransformₗᵢ ℝ ℂ (f : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ)
        (((Lp.fourierTransformₗᵢ ℝ ℂ (g : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) := by
    filter_upwards [logarithmicConvolution_factor_graph f, logarithmicConvolution_factor_graph g] with ξ hf hg
    let m := continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)
    have hmod : (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) = m * star m := by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact congrArg Complex.ofReal (continuedLogReferenceFactor_imaginary_norm_sq _).symm
    calc
      _ = star (m * (((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution f) : RealLineL2) : ℝ → ℂ) ξ)) *
          (m * (((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution g) : RealLineL2) : ℝ → ℂ) ξ)) := by
        rw [hmod, star_mul]
        ring
      _ = _ := by rw [hf, hg, RCLike.inner_apply', starRingEnd_apply]
  calc
    _ = ∫ ξ : ℝ, inner ℂ
        (((Lp.fourierTransformₗᵢ ℝ ℂ (f : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ)
        (((Lp.fourierTransformₗᵢ ℝ ℂ (g : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) := integral_congr_ae he
    _ = inner ℂ (Lp.fourierTransformₗᵢ ℝ ℂ (f : RealLineL2))
        (Lp.fourierTransformₗᵢ ℝ ℂ (g : RealLineL2)) := (L2.inner_def _ _).symm
    _ = inner ℂ f g := (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map _ _


/-- The literal logarithmic form is Hermitian, including its totalized integral values. -/
theorem logarithmicFullForm_conj (u v : RealLineL2) :
    star (logarithmicFullForm u v) = logarithmicFullForm v u := by
  unfold logarithmicFullForm
  simp only [RCLike.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- Every finite-energy whole-line source is an actual causal convolution of an L² source. -/
theorem hasLogarithmicEnergy_iff_range_convolution (u : RealLineL2) :
    HasLogarithmicEnergy u ↔ u ∈ LinearMap.range logarithmicConvolution.toLinearMap := by
  constructor
  · intro hu
    let F : ℝ → ℂ := fun ξ => continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
      fourierUnitary u ξ
    have hF : MemLp F 2 volume := hu
    let v : RealLineL2 := fourierUnitary.symm (hF.toLp F)
    have hv : (fourierUnitary v : ℝ → ℂ) =ᵐ[volume] F := by
      dsimp only [v]
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hF.coeFn_toLp
    exact ⟨v, logarithmicConvolution_eq_of_factor_graph hv⟩
  · rintro ⟨v, rfl⟩
    exact logarithmicConvolution_has_energy v

private def translationLoss (t : ℝ) : RealLineL2 →L[ℂ] RealLineL2 := logTranslationCLM t - 1

private def jumpLoss (f : RealLineL2) (t : ℝ) : ℝ :=
  logReferenceLevyDensity t * ‖translationLoss t f‖ ^ 2

private theorem jumpLoss_meas (f : RealLineL2) :
    AEStronglyMeasurable (jumpLoss f) (volume.restrict (Ioi (0 : ℝ))) :=
  measurable_logReferenceLevyDensity.aestronglyMeasurable.mul
    (((continuous_logTranslationCLM f).sub continuous_const).aestronglyMeasurable.norm.pow 2)

private theorem jumpLoss_nonneg (f : RealLineL2) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] jumpLoss f := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (logReferenceLevyDensity_nonneg ht.le) (sq_nonneg _)

private theorem integral_jumpLoss_fourier (f : RealLineL2) :
    (∫ t in Ioi (0 : ℝ), jumpLoss f t) = ∫ ξ : ℝ,
      (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) * ‖fourierUnitary f ξ‖ ^ 2 := by
  have hm : AEStronglyMeasurable (fun ξ : ℝ =>
      (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) * ‖fourierUnitary f ξ‖ ^ 2) volume :=
    (((continuous_positiveLogarithmicSymbol.comp (by fun_prop)).sub continuous_const).aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable (fourierUnitary f)).norm.pow 2)
  have hn : 0 ≤ᵐ[volume] fun ξ : ℝ =>
      (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) * ‖fourierUnitary f ξ‖ ^ 2 :=
    Eventually.of_forall fun ξ =>
      mul_nonneg (sub_nonneg.mpr (one_le_positiveLogarithmicSymbol _)) (sq_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae (jumpLoss_nonneg f) (jumpLoss_meas f),
    integral_eq_lintegral_of_nonneg_ae hn hm]
  exact congrArg ENNReal.toReal (logarithmicJumpEnergyL_eq_fourier f)

private def jumpLossC (f : RealLineL2) (t : ℝ) : ℂ := (jumpLoss f t : ℂ)

private theorem jumpLossC_integrable {f : RealLineL2} (hf : HasLogarithmicEnergy f) :
    IntegrableOn (jumpLossC f) (Ioi (0 : ℝ)) :=
  Complex.ofRealCLM.integrable_comp ((hasLogarithmicEnergy_iff_integrable_jump f).mp hf)

private theorem jumpLossC_integral {f : RealLineL2} (hf : HasLogarithmicEnergy f) :
    (∫ t in Ioi (0 : ℝ), jumpLossC f t) = logarithmicFullForm f f - inner ℂ f f := by
  have hinner : inner ℂ f f = ∫ ξ : ℝ, inner ℂ (fourierUnitary f ξ) (fourierUnitary f ξ) := by
    rw [← L2.inner_def]
    exact ((fourierUnitary).inner_map_map f f).symm
  unfold jumpLossC
  rw [integral_complex_ofReal, integral_jumpLoss_fourier, hinner]
  unfold logarithmicFullForm
  have hw : Integrable (fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
      star (fourierUnitary f ξ) * fourierUnitary f ξ) := integrable_logarithmicFullForm hf hf
  rw [← integral_sub hw (L2.integrable_inner (fourierUnitary f) (fourierUnitary f)),
    ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with ξ
  have hs : star (fourierUnitary f ξ) * fourierUnitary f ξ =
      ((‖fourierUnitary f ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [RCLike.inner_apply', starRingEnd_apply]
  simp only [mul_assoc, hs]
  push_cast
  ring

private theorem jumpMixed_polarization (f g : RealLineL2) (t : ℝ) :
    (logReferenceLevyDensity t : ℂ) * inner ℂ (translationLoss t f) (translationLoss t g) =
      ((jumpLossC (f+g) t - jumpLossC (f-g) t) +
        (jumpLossC (f-I•g) t - jumpLossC (f+I•g) t)*I)/4 := by
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [jumpLossC, jumpLoss, map_add, map_sub, map_smul]
  push_cast
  change (logReferenceLevyDensity t : ℂ) *
    ((↑‖translationLoss t f + translationLoss t g‖ ^ 2 -
      ↑‖translationLoss t f - translationLoss t g‖ ^ 2 +
      (↑‖translationLoss t f-I•translationLoss t g‖ ^ 2 -
        ↑‖translationLoss t f+I•translationLoss t g‖ ^ 2)*I)/4) = _
  ring

private theorem energy_add {f g : RealLineL2} (hf : HasLogarithmicEnergy f) (hg : HasLogarithmicEnergy g) :
    HasLogarithmicEnergy (f + g) := by
  rw [hasLogarithmicEnergy_iff_range_convolution] at hf hg ⊢
  exact (LinearMap.range logarithmicConvolution.toLinearMap).add_mem hf hg

private theorem energy_sub {f g : RealLineL2} (hf : HasLogarithmicEnergy f) (hg : HasLogarithmicEnergy g) :
    HasLogarithmicEnergy (f - g) := by
  rw [hasLogarithmicEnergy_iff_range_convolution] at hf hg ⊢
  exact (LinearMap.range logarithmicConvolution.toLinearMap).sub_mem hf hg

private theorem energy_smul (c : ℂ) {f : RealLineL2} (hf : HasLogarithmicEnergy f) :
    HasLogarithmicEnergy (c • f) := by
  rw [hasLogarithmicEnergy_iff_range_convolution] at hf ⊢
  exact (LinearMap.range logarithmicConvolution.toLinearMap).smul_mem c hf

/-- Mixed translation losses are absolutely integrable throughout the logarithmic form domain. -/
theorem integrable_logarithmicJumpMixed {f g : RealLineL2}
    (hf : HasLogarithmicEnergy f) (hg : HasLogarithmicEnergy g) :
    IntegrableOn (fun t : ℝ => (logReferenceLevyDensity t : ℂ) *
      inner ℂ (logTranslationCLM t f - f) (logTranslationCLM t g - g)) (Ioi 0) := by
  have h := ((jumpLossC_integrable (energy_add hf hg)).sub
    (jumpLossC_integrable (energy_sub hf hg))).add
      (((jumpLossC_integrable (energy_sub hf (energy_smul I hg))).sub
        (jumpLossC_integrable (energy_add hf (energy_smul I hg)))).mul_const I)
  refine (h.div_const 4).congr (Eventually.of_forall fun t => ?_)
  exact (jumpMixed_polarization f g t).symm

/-- The complete complex logarithmic form equals mass plus the literal mixed jump pairing. -/
theorem logarithmicFullForm_eq_inner_add_jump {f g : RealLineL2}
    (hf : HasLogarithmicEnergy f) (hg : HasLogarithmicEnergy g) :
    logarithmicFullForm f g = inner ℂ f g + ∫ t in Ioi (0 : ℝ),
      (logReferenceLevyDensity t : ℂ) *
        inner ℂ (logTranslationCLM t f - f) (logTranslationCLM t g - g) := by
  obtain ⟨u, rfl⟩ := (hasLogarithmicEnergy_iff_range_convolution f).mp hf
  obtain ⟨v, rfl⟩ := (hasLogarithmicEnergy_iff_range_convolution g).mp hg
  change HasLogarithmicEnergy (logarithmicConvolution u) at hf
  change HasLogarithmicEnergy (logarithmicConvolution v) at hg
  have hpoint := fun t => jumpMixed_polarization (logarithmicConvolution u) (logarithmicConvolution v) t
  change logarithmicFullForm (logarithmicConvolution u) (logarithmicConvolution v) =
    inner ℂ (logarithmicConvolution u) (logarithmicConvolution v) + ∫ t in Ioi (0 : ℝ),
      (logReferenceLevyDensity t : ℂ) *
        inner ℂ (translationLoss t (logarithmicConvolution u)) (translationLoss t (logarithmicConvolution v))
  simp_rw [hpoint]
  have hA := jumpLossC_integrable (energy_add hf hg)
  have hB := jumpLossC_integrable (energy_sub hf hg)
  have hC := jumpLossC_integrable (energy_sub hf (energy_smul I hg))
  have hD := jumpLossC_integrable (energy_add hf (energy_smul I hg))
  have ha := integral_add (hA.sub hB) ((hC.sub hD).mul_const I)
  have hb := integral_sub hA hB
  have hc := integral_sub hC hD
  simp only [Pi.sub_apply] at ha hb hc
  rw [integral_div, ha, integral_mul_const, hb, hc]
  rw [jumpLossC_integral (energy_add hf hg), jumpLossC_integral (energy_sub hf hg),
    jumpLossC_integral (energy_sub hf (energy_smul I hg)),
    jumpLossC_integral (energy_add hf (energy_smul I hg))]
  simp only [← map_add, ← map_sub, ← map_smul, logarithmicFullForm_convolution]
  rw [inner_eq_sum_norm_sq_div_four u v,
    inner_eq_sum_norm_sq_div_four (logarithmicConvolution u) (logarithmicConvolution v)]
  simp only [inner_self_eq_norm_sq_to_K, map_add, map_sub, map_smul]
  simp only [show (RCLike.I : ℂ) = I from rfl]
  ring!

private theorem logarithmicTranslations_commute (s t : ℝ) (f : RealLineL2) :
    logTranslationCLM t (logTranslationCLM s f) = logTranslationCLM s (logTranslationCLM t f) := by
  have hst := (logarithmicTranslation_coeFn s f).comp_tendsto
    (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.tendsto_ae
  have hts := (logarithmicTranslation_coeFn t f).comp_tendsto
    (MellinL2.realTranslation_measurePreserving s).quasiMeasurePreserving.tendsto_ae
  apply Lp.ext
  filter_upwards [logarithmicTranslation_coeFn t (logTranslationCLM s f),
    logarithmicTranslation_coeFn s (logTranslationCLM t f), hst, hts] with x h1 h2 h3 h4
  change (logTranslationCLM s f) (x + t) = f ((x + t) + s) at h3
  change (logTranslationCLM t f) (x + s) = f ((x + s) + t) at h4
  rw [h1, h2, h3, h4]
  congr 1
  ring

private theorem logarithmicTranslationLoss_commute (s t : ℝ) (f : RealLineL2) :
    logTranslationCLM t (logTranslationCLM s f) - logTranslationCLM s f =
      logTranslationCLM s (logTranslationCLM t f - f) := by
  rw [map_sub, logarithmicTranslations_commute]

/-- Translating physical support preserves the full logarithmic energy domain. -/
theorem hasLogarithmicEnergy_translation (s : ℝ) {f : RealLineL2} (hf : HasLogarithmicEnergy f) :
    HasLogarithmicEnergy (logTranslationCLM s f) := by
  rw [hasLogarithmicEnergy_iff_integrable_jump] at hf ⊢
  apply hf.congr
  filter_upwards with t
  rw [logarithmicTranslationLoss_commute]
  congr 1
  exact congrArg (fun r : ℝ => r ^ 2) ((MellinL2.additiveTranslationUnitary s).norm_map _).symm

/-- Translating both sources leaves the actual complete logarithmic form unchanged. -/
theorem logarithmicFullForm_translation (s : ℝ) {f g : RealLineL2}
    (hf : HasLogarithmicEnergy f) (hg : HasLogarithmicEnergy g) :
    logarithmicFullForm (logTranslationCLM s f) (logTranslationCLM s g) =
      logarithmicFullForm f g := by
  have hinner (u v : RealLineL2) :
      inner ℂ (logTranslationCLM s u) (logTranslationCLM s v) = inner ℂ u v :=
    (MellinL2.additiveTranslationUnitary s).inner_map_map _ _
  rw [logarithmicFullForm_eq_inner_add_jump (hasLogarithmicEnergy_translation s hf)
    (hasLogarithmicEnergy_translation s hg), logarithmicFullForm_eq_inner_add_jump hf hg,
    hinner f g]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [logarithmicTranslationLoss_commute, logarithmicTranslationLoss_commute,
    hinner]

#print axioms logarithmicFullForm_translation
#print axioms logarithmicFullForm_eq_inner_add_jump
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
