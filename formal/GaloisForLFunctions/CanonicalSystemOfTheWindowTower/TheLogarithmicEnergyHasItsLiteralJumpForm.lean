import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheHalfLineLogarithmicFormHasItsActualInverse
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilSymbolIsALogarithmicMultiplierPlusABoundedKernel
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadGammaAutocorrelationEnergy

/-!
# The literal logarithmic jump energy

Plancherel at each translation and Tonelli identify the extended jump energy
of every physical L² source with its positive logarithmic Fourier energy
minus mass. Finiteness is exactly the actual logarithmic multiplier domain.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform ENNReal InnerProductSpace
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

theorem logReferenceLevyDensity_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ logReferenceLevyDensity t :=
  div_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) ht)

theorem measurable_logReferenceLevyDensity : Measurable logReferenceLevyDensity := by
  unfold logReferenceLevyDensity
  fun_prop

/-- The full logarithmic jump energy of an actual L² source, allowing infinite energy. -/
def logarithmicJumpEnergyL (f : RealLineL2) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
    (logReferenceLevyDensity t * ‖logTranslationCLM t f - f‖ ^ 2)

private theorem logarithmicTranslationDefect_fourier (f : RealLineL2) (t : ℝ) :
    ‖logTranslationCLM t f - f‖ ^ 2 = ∫ ξ : ℝ,
      (2 - 2 * Real.cos (2 * Real.pi * t * ξ)) * ‖fourierUnitary f ξ‖ ^ 2 := by
  have h := ccmActualHeadTranslationDefect_fourierUnitary_symm t (fourierUnitary f)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h

private theorem integrable_logarithmicCosineWeight (ξ : ℝ) :
    IntegrableOn (fun t : ℝ => logReferenceLevyDensity t *
      (2 - 2 * Real.cos (2 * Real.pi * t * ξ))) (Ioi 0) := by
  have h := integrableOn_abelLogKernelIntegrand (delta := 1) (b := 2 * Real.pi * ξ) (by norm_num)
  apply h.congr
  filter_upwards with t
  unfold logReferenceLevyDensity abelLogKernelIntegrand
  rw [one_mul, show 2 * Real.pi * t * ξ = (2 * Real.pi * ξ) * t by ring]
  ring

private theorem integral_logarithmicCosineWeight (ξ : ℝ) :
    (∫ t in Ioi (0 : ℝ), logReferenceLevyDensity t *
      (2 - 2 * Real.cos (2 * Real.pi * t * ξ))) = positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1 := by
  calc
    _ = 2 * ∫ t in Ioi (0 : ℝ), logReferenceLevyDensity t *
        (1 - Real.cos ((2 * Real.pi * ξ) * t)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [show 2 * Real.pi * t * ξ = (2 * Real.pi * ξ) * t by ring]
      ring
    _ = _ := by rw [logReferenceLevyDensity_symbol]; unfold positiveLogarithmicSymbol; ring

private def logarithmicJointKernel (F : RealLineL2) (t ξ : ℝ) : ℝ :=
  logReferenceLevyDensity t * ((2 - 2 * Real.cos (2 * Real.pi * t * ξ)) * ‖F ξ‖ ^ 2)

private theorem measurable_logarithmicJointKernel (F : RealLineL2) :
    Measurable (Function.uncurry (logarithmicJointKernel F)) := by
  exact (measurable_logReferenceLevyDensity.comp measurable_fst).mul
    ((by fun_prop : Measurable (fun p : ℝ × ℝ => 2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2))).mul
      (((Lp.stronglyMeasurable F).measurable.comp measurable_snd).norm.pow_const 2))

private theorem logarithmicJumpEnergyL_eq_joint (f : RealLineL2) :
    logarithmicJumpEnergyL f = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ξ : ℝ,
      ENNReal.ofReal (logarithmicJointKernel (fourierUnitary f) t ξ) := by
  unfold logarithmicJumpEnergyL
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change ENNReal.ofReal (logReferenceLevyDensity t * ‖logTranslationCLM t f - f‖ ^ 2) =
    ∫⁻ ξ : ℝ, ENNReal.ofReal (logarithmicJointKernel (fourierUnitary f) t ξ)
  rw [logarithmicTranslationDefect_fourier]
  have hi := integrable_ccmGammaCosineDefectSpectralDensity t (fourierUnitary f)
  have hn := ccmGammaCosineDefectSpectralDensity_nonneg t (fourierUnitary f)
  rw [ENNReal.ofReal_mul (logReferenceLevyDensity_nonneg ht.le),
    ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)]
  rw [← lintegral_const_mul'' _ hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  apply lintegral_congr
  intro ξ
  exact (ENNReal.ofReal_mul (logReferenceLevyDensity_nonneg ht.le)).symm

private theorem lintegral_logarithmicJointKernel (F : RealLineL2) (ξ : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (logarithmicJointKernel F t ξ)) =
      ENNReal.ofReal ((positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) * ‖F ξ‖ ^ 2) := by
  have hi : IntegrableOn (fun t : ℝ => logarithmicJointKernel F t ξ) (Ioi 0) :=
    ((integrable_logarithmicCosineWeight ξ).mul_const (‖F ξ‖ ^ 2)).congr
      (Eventually.of_forall fun t => mul_assoc _ _ _)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => logarithmicJointKernel F t ξ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (logReferenceLevyDensity_nonneg ht.le)
      (ccmGammaCosineDefectSpectralDensity_nonneg t F ξ)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  calc
    _ = (∫ t in Ioi (0 : ℝ), logReferenceLevyDensity t *
        (2 - 2 * Real.cos (2 * Real.pi * t * ξ))) * ‖F ξ‖ ^ 2 := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with t
      exact (mul_assoc _ _ _).symm
    _ = _ := by rw [integral_logarithmicCosineWeight]

/-- Plancherel and Tonelli identify the literal jump energy on every L² vector. -/
theorem logarithmicJumpEnergyL_eq_fourier (f : RealLineL2) :
    logarithmicJumpEnergyL f = ∫⁻ ξ : ℝ, ENNReal.ofReal
      ((positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) * ‖fourierUnitary f ξ‖ ^ 2) := by
  rw [logarithmicJumpEnergyL_eq_joint,
    lintegral_lintegral_swap (measurable_logarithmicJointKernel (fourierUnitary f)).ennreal_ofReal.aemeasurable]
  exact lintegral_congr (lintegral_logarithmicJointKernel (fourierUnitary f))

private theorem integrable_logarithmic_excess_iff (f : RealLineL2) :
    Integrable (fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) *
      ‖fourierUnitary f ξ‖ ^ 2) ↔ HasLogarithmicEnergy f := by
  have hsq : Integrable (fun ξ : ℝ => ‖fourierUnitary f ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  rw [hasLogarithmicEnergy_iff_integrable]
  constructor
  · intro h
    apply (h.add hsq).congr
    filter_upwards with ξ
    change (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) * ‖fourierUnitary f ξ‖ ^ 2 +
      ‖fourierUnitary f ξ‖ ^ 2 = positiveLogarithmicSymbol (2 * Real.pi * ξ) * ‖fourierUnitary f ξ‖ ^ 2
    ring
  · intro h
    apply (h.sub hsq).congr
    filter_upwards with ξ
    change positiveLogarithmicSymbol (2 * Real.pi * ξ) * ‖fourierUnitary f ξ‖ ^ 2 -
      ‖fourierUnitary f ξ‖ ^ 2 = (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) * ‖fourierUnitary f ξ‖ ^ 2
    ring

/-- The literal logarithmic Fourier domain is exactly finiteness of the actual jump energy. -/
theorem hasLogarithmicEnergy_iff_jumpEnergy_ne_top (f : RealLineL2) :
    HasLogarithmicEnergy f ↔ logarithmicJumpEnergyL f ≠ ⊤ := by
  rw [logarithmicJumpEnergyL_eq_fourier]
  have hm : AEStronglyMeasurable (fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) *
      ‖fourierUnitary f ξ‖ ^ 2) volume :=
    (((continuous_positiveLogarithmicSymbol.comp (by fun_prop)).sub continuous_const).aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable (fourierUnitary f)).norm.pow 2)
  have hn : 0 ≤ᵐ[volume] fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) *
      ‖fourierUnitary f ξ‖ ^ 2 := Eventually.of_forall fun ξ =>
    mul_nonneg (sub_nonneg.mpr (one_le_positiveLogarithmicSymbol _)) (sq_nonneg _)
  rw [lintegral_ofReal_ne_top_iff_integrable hm hn, integrable_logarithmic_excess_iff]

/-- Finite Fourier energy is equivalent to absolute integrability of literal translation losses. -/
theorem hasLogarithmicEnergy_iff_integrable_jump (f : RealLineL2) :
    HasLogarithmicEnergy f ↔ IntegrableOn (fun t : ℝ =>
      logReferenceLevyDensity t * ‖logTranslationCLM t f - f‖ ^ 2) (Ioi 0) := by
  have hc : Continuous (fun t : ℝ => logTranslationCLM t f - f) :=
    (continuous_logTranslationCLM f).sub continuous_const
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      logReferenceLevyDensity t * ‖logTranslationCLM t f - f‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    measurable_logReferenceLevyDensity.aestronglyMeasurable.mul
      (hc.aestronglyMeasurable.norm.pow 2)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t =>
      logReferenceLevyDensity t * ‖logTranslationCLM t f - f‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (logReferenceLevyDensity_nonneg ht.le) (sq_nonneg _)
  rw [hasLogarithmicEnergy_iff_jumpEnergy_ne_top, logarithmicJumpEnergyL,
    lintegral_ofReal_ne_top_iff_integrable hm hn]
  rfl

#print axioms logarithmicJumpEnergyL_eq_fourier
#print axioms hasLogarithmicEnergy_iff_jumpEnergy_ne_top
#print axioms hasLogarithmicEnergy_iff_integrable_jump

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
