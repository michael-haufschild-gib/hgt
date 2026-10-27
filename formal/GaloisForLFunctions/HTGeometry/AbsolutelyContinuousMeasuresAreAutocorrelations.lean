import GaloisForLFunctions.HTGeometry.FourierTranslationModulation
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Absolutely continuous measures are L² autocorrelations

The square root of a finite measure's Radon–Nikodym density is an L² wave.
The inverse unitary Fourier transform realizes its characteristic function
as a translation autocorrelation. Rescaling frequencies accounts for the
Fourier convention with the factor `2π`; the wave's squared norm is exactly
the original measure's mass.
-/

open MeasureTheory Complex FourierTransform Set
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The square root of the Lebesgue density defines an L² wave. -/
theorem exists_L2_rnDeriv_wave (μ : Measure ℝ) [IsFiniteMeasure μ] : ∃ G : Lp ℂ 2 (volume : Measure ℝ),
      (fun x => ‖G x‖ ^ 2) =ᵐ[volume] fun x => (μ.rnDeriv volume x).toReal := by
  let g : ℝ → ℂ := fun x => (Real.sqrt (μ.rnDeriv volume x).toReal : ℂ)
  have hgmeas : AEStronglyMeasurable g volume :=
    (Complex.continuous_ofReal.comp Real.continuous_sqrt).comp_aestronglyMeasurable
      (Measure.integrable_toReal_rnDeriv (μ := μ) (ν := volume)).aestronglyMeasurable
  have hgsq (x : ℝ) : ‖g x‖ ^ 2 = (μ.rnDeriv volume x).toReal := by
    dsimp only [g]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt ENNReal.toReal_nonneg]
  have hg : MemLp g 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hgmeas]
    simpa only [hgsq] using (Measure.integrable_toReal_rnDeriv (μ := μ) (ν := volume))
  refine ⟨hg.toLp g, ?_⟩
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx, hgsq]

/-- Plancherel turns a finite density into a translation autocorrelation. -/
theorem exists_L2_autocorrelation_density (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) : ∃ H : Lp ℂ 2 (volume : Measure ℝ),
      (∀ t : ℝ, (∫ x, H (x + t) * conj (H x)) = ∫ x, modulationSymbol t x ∂μ) ∧
      (∫ x, ‖H x‖ ^ 2) = μ.real univ := by
  obtain ⟨G, hG⟩ := exists_L2_rnDeriv_wave μ
  let H : Lp ℂ 2 (volume : Measure ℝ) := (Lp.fourierTransformₗᵢ ℝ ℂ).symm G
  have hHG : (𝓕 H : Lp ℂ 2 (volume : Measure ℝ)) = G :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply G
  refine ⟨H, ?_, ?_⟩
  · intro t
    have hcorr : (∫ x, H (x + t) * conj (H x)) = ⟪H, translateL2 t H⟫_ℂ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coeFn_translateL2 t H] with x hx
      rw [hx, RCLike.inner_apply]
    rw [hcorr, ← Lp.inner_fourier_eq H (translateL2 t H),
      fourierTransform_translateL2, hHG, L2.inner_def]
    calc (∫ x, ⟪G x, (modulationMul t G) x⟫_ℂ)
        = ∫ x, (μ.rnDeriv volume x).toReal • modulationSymbol t x := by
          apply integral_congr_ae
          filter_upwards [coeFn_modulationMul t G, hG] with x hx hnorm
          rw [hx, RCLike.inner_apply, Complex.real_smul]
          calc modulationSymbol t x * G x * conj (G x)
              = modulationSymbol t x * ((‖G x‖ ^ 2 : ℝ) : ℂ) := by
                rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
            _ = _ := by rw [hnorm]; ring
      _ = ∫ x, modulationSymbol t x ∂μ := integral_rnDeriv_smul hμ
  · rw [← _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq volume H,
      show ‖H‖ = ‖G‖ from (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map G,
      _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq volume G,
      integral_congr_ae hG]
    exact Measure.integral_toReal_rnDeriv hμ

/-- Every finite absolutely continuous measure is the dilation-frequency law of an L² wave. -/
theorem exists_L2_autocorrelation_eq_charFun (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν ≪ volume) : ∃ H : Lp ℂ 2 (volume : Measure ℝ),
      (∀ t : ℝ, (∫ x, H (x + t) * conj (H x)) = charFun ν t) ∧
      (∫ x, ‖H x‖ ^ 2) = ν.real univ := by
  let c : ℝ := (2 * Real.pi)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (by positivity)
  have hf : Measurable (fun x : ℝ => x * c) := measurable_id.mul_const c
  let μ := ν.map (fun x : ℝ => x * c)
  have hμ : μ ≪ volume := by
    have h := hν.map hf
    rw [Real.map_volume_mul_right hc] at h
    exact h.trans Measure.smul_absolutelyContinuous
  obtain ⟨H, hcorr, hmass⟩ := exists_L2_autocorrelation_density μ hμ
  refine ⟨H, ?_, ?_⟩
  · intro t
    rw [hcorr, charFun_apply_real]
    change (∫ x, modulationSymbol t x ∂ν.map (fun x : ℝ => x * c)) = _
    rw [integral_map hf.aemeasurable (measurable_modulationSymbol t).aestronglyMeasurable]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only [Function.comp_apply, modulationSymbol]
    congr 1
    dsimp only [c]
    push_cast
    field_simp
  · rw [hmass]
    simp only [μ, measureReal_def, Measure.map_apply hf MeasurableSet.univ, preimage_univ]

#print axioms exists_L2_autocorrelation_eq_charFun

end GaloisForLFunctions.HTGeometry
