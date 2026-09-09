import GaloisForLFunctions.RHTower.FokasLenellsOperatorNormObstruction
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation
import GaloisForLFunctions.HTGeometry.LinftyMultiplicationNorm

/-!
# Cauchy compression preserves actual multiplier norms

Modulation translates the inverse Fourier transform. Moving that translate
far into the positive datum ray asymptotically captures its entire norm in
the negative Cauchy projection. Consequently that projection cannot hide
any multiplier operator-norm obstruction.
-/

open MeasureTheory Complex Matrix Filter Topology Set FourierTransform
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem cutoff_positive_translate (a : ℝ) (u : SoninL2) :
    indicatorCutoff (Ioi 0) measurableSet_Ioi (translateL2 a u) =
      translateL2 a (indicatorCutoff (Ioi a) measurableSet_Ioi u) := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Ioi 0) measurableSet_Ioi (translateL2 a u),
    coeFn_translateL2 a u,coeFn_translateL2 a (indicatorCutoff (Ioi a) measurableSet_Ioi u),
    (indicatorCutoff_ae (Ioi a) measurableSet_Ioi u).comp_tendsto
      (measurePreserving_add_right (volume : Measure ℝ) a).quasiMeasurePreserving.tendsto_ae]
    with z h0 h1 h2 h3
  change (indicatorCutoff (Ioi a) measurableSet_Ioi u) (z+a) = (Ioi a).indicator (fun y => u y) (z+a) at h3
  rw [h0,h2,h3]
  by_cases hz : z ∈ Ioi (0:ℝ)
  · have hza : z+a ∈ Ioi a := by change a < z+a; change 0 < z at hz; linarith
    simp only [indicator_of_mem hz,indicator_of_mem hza,h1]
  · have hza : z+a ∉ Ioi a := by change ¬ a < z+a; change ¬ 0 < z at hz; linarith
    simp only [indicator_of_notMem hz,indicator_of_notMem hza]

/-- Increasing datum half-lines exhaust every vector in the existing Sonin L2 carrier. -/
theorem indicatorCutoff_Ioi_tendsto_atBot (u : SoninL2) :
    Tendsto (fun a : ℝ => indicatorCutoff (Ioi a) measurableSet_Ioi u) atBot (𝓝 u) := by
  let φ (a z : ℝ) : ℂ := (Ioi a).indicator (fun _ => (1:ℂ)) z
  have hm (a : ℝ) : Measurable (φ a) := measurable_const.indicator measurableSet_Ioi
  have hb (a z : ℝ) : ‖φ a z‖ ≤ (1:ℝ) := by
    by_cases hz : z ∈ Ioi a <;> simp [φ,hz]
  have hi (z : ℝ) : ‖(1:ℂ)‖ ≤ (1:ℝ) := by norm_num
  have hp (z : ℝ) : Tendsto (fun a => φ a z) atBot (𝓝 (1:ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot z] with a ha
    simp [φ,ha]
  have ht := tendsto_lpBoundedMulCLM_apply (μ := volume) hm measurable_const (by positivity : (0:ℝ) ≤ 1) hb hi hp u
  have he (a : ℝ) : lpBoundedMulCLM (p := 2) (μ := volume) (hm a) (by positivity : (0:ℝ) ≤ 1) (hb a) u =
      indicatorCutoff (Ioi a) measurableSet_Ioi u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) (hm a) (by positivity : (0:ℝ) ≤ 1) (hb a) u,
      indicatorCutoff_ae (Ioi a) measurableSet_Ioi u] with z h1 h2
    rw [h1,h2]
    by_cases hz : z ∈ Ioi a <;> simp [φ,hz]
  have he1 : lpBoundedMulCLM (p := 2) (μ := volume) measurable_const (by positivity : (0:ℝ) ≤ 1) hi u = u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) measurable_const (by positivity : (0:ℝ) ≤ 1) hi u] with z hz
    simpa only [one_mul] using hz
  simpa only [he,he1] using ht

private theorem fourier_translated_inverse_eq_modulation (a : ℝ) (u : SoninL2) :
    fourierUnitary (translateL2 a (fourierUnitary.symm u)) = modulationMul a u := by
  have h := fourierTransform_translateL2 a (fourierUnitary.symm u)
  change fourierUnitary (translateL2 a (fourierUnitary.symm u)) =
    modulationMul a (fourierUnitary (fourierUnitary.symm u)) at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

/-- The modulation used to probe Hardy compression preserves the entire L2 norm. -/
theorem norm_modulationMul_eq (a : ℝ) (u : SoninL2) : ‖modulationMul a u‖ = ‖u‖ := by
  rw [← fourier_translated_inverse_eq_modulation,fourierUnitary.norm_map,(translateL2 a).norm_map,fourierUnitary.symm.norm_map]

/-- Cauchy compression of a modulated vector is exactly a translated half-line cutoff in norm. -/
theorem negativeCauchy_modulation_norm_eq_cutoff (a : ℝ) (u : SoninL2) :
    ‖negativeCauchy (modulationMul a u)‖ = ‖indicatorCutoff (Ioi a) measurableSet_Ioi (fourierUnitary.symm u)‖ := by
  rw [← fourier_translated_inverse_eq_modulation]
  change ‖-fourierUnitary (indicatorCutoff (Ioi 0) measurableSet_Ioi
    (fourierUnitary.symm (fourierUnitary (translateL2 a (fourierUnitary.symm u)))))‖ = _
  rw [LinearIsometryEquiv.symm_apply_apply,norm_neg,fourierUnitary.norm_map,
    cutoff_positive_translate,(translateL2 a).norm_map]

/-- Modulation into the selected Hardy direction makes Cauchy compression recover the full input norm. -/
theorem negativeCauchy_modulation_norm_tendsto (u : SoninL2) :
    Tendsto (fun a : ℝ => ‖negativeCauchy (modulationMul a u)‖) atBot (𝓝 ‖u‖) := by
  simpa only [negativeCauchy_modulation_norm_eq_cutoff,fourierUnitary.symm.norm_map] using
    (indicatorCutoff_Ioi_tendsto_atBot (fourierUnitary.symm u)).norm

private theorem multiplier_commutes_modulation (T : SoninL2 →L[ℂ] SoninL2) (φ : ℝ → ℂ)
    (hT : ∀ u : SoninL2, (T u : ℝ → ℂ) =ᵐ[volume] fun z => φ z*u z) (a : ℝ) (u : SoninL2) :
    T (modulationMul a u) = modulationMul a (T u) := by
  apply Lp.ext
  filter_upwards [hT (modulationMul a u),coeFn_modulationMul a u,coeFn_modulationMul a (T u),hT u]
    with z h0 h1 h2 h3
  rw [h0,h1,h2,h3]
  ring

private theorem cauchy_compression_norm_of_multiplier (T : SoninL2 →L[ℂ] SoninL2) (φ : ℝ → ℂ)
    (hT : ∀ u : SoninL2, (T u : ℝ → ℂ) =ᵐ[volume] fun z => φ z*u z) :
    ‖negativeCauchy.comp T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro u
    exact (negativeCauchy_bound (T u)).trans (T.le_opNorm u)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (negativeCauchy.comp T))
    intro u
    apply le_of_tendsto (negativeCauchy_modulation_norm_tendsto (T u))
    apply Eventually.of_forall
    intro a
    have h := (negativeCauchy.comp T).le_opNorm (modulationMul a u)
    change ‖negativeCauchy (T (modulationMul a u))‖ ≤ _ at h
    rw [multiplier_commutes_modulation T φ hT,norm_modulationMul_eq] at h
    exact h

/-- Cauchy compression preserves the full essential-supremum norm of every measurable bounded symbol. -/
theorem norm_negativeCauchy_comp_lineLinftyMultiplier
    (g : Lp ℂ ∞ (volume : Measure ℝ)) :
    ‖negativeCauchy.comp (lineLinftyMultiplier g)‖ = ‖g‖ := by
  rw [cauchy_compression_norm_of_multiplier _ _ (lineLinftyMultiplier_ae g),
    norm_lineLinftyMultiplier]

/-- The actual bounded scattering multiplier loses no operator norm under the signed Cauchy projection. -/
theorem norm_negativeCauchy_comp_directMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖negativeCauchy.comp (directMultiplier q t x reverse)‖ = ‖directMultiplier q t x reverse‖ :=
  cauchy_compression_norm_of_multiplier _ _ (directMultiplier_ae q t x reverse)

/-- The same norm preservation holds for the actual first-time generator. -/
theorem norm_negativeCauchy_comp_directTimeMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖negativeCauchy.comp (directTimeMultiplier q t x reverse)‖ = ‖directTimeMultiplier q t x reverse‖ :=
  cauchy_compression_norm_of_multiplier _ _ (directTimeMultiplier_ae q t x reverse)

/-- Cauchy compression cannot remove the actual time difference-quotient error. -/
theorem norm_negativeCauchy_comp_directTimeSlopeError (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (reverse : Bool) :
    ‖negativeCauchy.comp (slope (fun r => directMultiplier q r x reverse) t s-directTimeMultiplier q t x reverse)‖ =
      ‖slope (fun r => directMultiplier q r x reverse) t s-directTimeMultiplier q t x reverse‖ :=
  cauchy_compression_norm_of_multiplier _ _ (directMultiplier_time_slope_error_ae q t s x reverse)

end
end RHTower.FokasLenells
