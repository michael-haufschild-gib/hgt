import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Finite volume of the modular fundamental domain and positivity of `dx dy / y²`

The modular fundamental domain `𝒟` lies in the union of the two translates `S`, `T⁻¹ S` of the
truncated strip `S = {0 ≤ Re z < 1, Im z ≥ √3/2}`, whose measure is finite because
`∫_{√3/2}^∞ y^{-2} dy < ∞`.  Separately, the invariant measure gives positive mass to every
nonempty open subset of `ℍ`, since it is Lebesgue measure on the open set `ℍ ⊆ ℂ` with the
strictly positive density `y^{-2}`.
-/

open UpperHalfPlane MeasureTheory Set ModularGroup Filter
open scoped NNReal ENNReal Pointwise MatrixGroups

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The truncated strip has finite volume -/

/-- The indicator of `{Im z ≥ c}` is integrable on the strip for `c > 0`. -/
theorem integrableOn_indicator_im_ge_modularStrip {c : ℝ} (hc : 0 < c) :
    IntegrableOn ({z : ℍ | c ≤ z.im}.indicator fun _ => (1 : ℂ)) modularStrip volume := by
  rw [integrableOn_modularStrip_iff, Measure.volume_eq_prod]
  have hR : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) :=
    measurableSet_Ioi.prod measurableSet_Ico
  have hg₀ : IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℂ)) (Ici c) volume := by
    have h1 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi (c / 2)) volume :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by positivity)
    have h2 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ici c) volume :=
      h1.mono_set fun y hy => lt_of_lt_of_le (by linarith : c / 2 < c) hy
    have h3 : IntegrableOn (fun y : ℝ => ((y ^ (-2 : ℝ) : ℝ) : ℂ)) (Ici c) volume := h2.ofReal
    refine h3.congr_fun (fun y hy => ?_) measurableSet_Ici
    have hy' : 0 < y := lt_of_lt_of_le hc hy
    show ((y ^ (-2 : ℝ) : ℝ) : ℂ) = ((y : ℂ) ^ 2)⁻¹
    rw [Real.rpow_neg hy'.le, Real.rpow_two, Complex.ofReal_inv, Complex.ofReal_pow]
  have hg : Integrable ((Ici c).indicator fun y : ℝ => ((y ^ 2)⁻¹ : ℂ)) (volume.restrict (Ioi 0)) :=
    (hg₀.integrable_indicator measurableSet_Ici).restrict
  have h1 : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Ico (0 : ℝ) 1)) :=
    integrableOn_const (by simp)
  have hG : IntegrableOn (fun p : ℝ × ℝ => (Ici c).indicator (fun y : ℝ => ((y ^ 2)⁻¹ : ℂ)) p.1 * 1)
      (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hg.mul_prod h1
  refine hG.congr_fun (fun p hp => ?_) hR
  have hy : (0 : ℝ) < p.1 := hp.1
  have him : (ofComplex (⟨p.2, p.1⟩ : ℂ)).im = p.1 := by
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  simp only [stripChartIntegrand, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ici, him,
    mul_one]
  split_ifs <;> simp

/-- The truncated strip `{0 ≤ Re z < 1, Im z ≥ c}` has finite volume. -/
theorem volume_modularStrip_inter_im_ge_lt_top {c : ℝ} (hc : 0 < c) :
    (volume : Measure ℍ) (modularStrip ∩ {z : ℍ | c ≤ z.im}) < ∞ := by
  have hmeas : MeasurableSet {z : ℍ | c ≤ z.im} := measurableSet_Ici.preimage continuous_im.measurable
  have h := integrableOn_indicator_im_ge_modularStrip hc
  rw [IntegrableOn, integrable_indicator_iff hmeas, IntegrableOn, Measure.restrict_restrict hmeas,
    ← IntegrableOn, integrableOn_const_iff] at h
  rcases h with h | h
  · simp at h
  · rwa [inter_comm]

/-! ## `𝒟` has finite volume -/

/-- `𝒟` is contained in the union of the truncated strip and its translate by `T⁻¹`. -/
theorem fd_subset_union_translate :
    fd ⊆ (modularStrip ∩ {z : ℍ | Real.sqrt 3 / 2 ≤ z.im}) ∪
      ModularGroup.T⁻¹ • (modularStrip ∩ {z : ℍ | Real.sqrt 3 / 2 ≤ z.im}) := by
  intro z hz
  have him : Real.sqrt 3 / 2 ≤ z.im := by
    have h3 := three_le_four_mul_im_sq_of_mem_fd hz
    have hy := z.im_pos
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [show Real.sqrt 3 = Real.sqrt 3 from rfl]
    have : Real.sqrt 3 ≤ Real.sqrt ((2 * z.im) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rw [Real.sqrt_sq (by positivity)] at this
    linarith
  have hre : |z.re| ≤ 1 / 2 := hz.2
  rw [abs_le] at hre
  rcases le_or_gt 0 z.re with h0 | h0
  · left
    exact ⟨⟨h0, by linarith⟩, him⟩
  · right
    refine ⟨ModularGroup.T • z, ⟨⟨?_, ?_⟩, ?_⟩, inv_smul_smul _ _⟩
    · rw [re_T_smul]; linarith
    · rw [re_T_smul]; linarith
    · show Real.sqrt 3 / 2 ≤ (ModularGroup.T • z).im
      rw [im_T_smul]; exact him

/-- **The modular fundamental domain has finite volume.** -/
theorem volume_fd_lt_top : (volume : Measure ℍ) fd < ∞ := by
  have hS := volume_modularStrip_inter_im_ge_lt_top (c := Real.sqrt 3 / 2) (by positivity)
  calc (volume : Measure ℍ) fd
      ≤ volume ((modularStrip ∩ {z : ℍ | Real.sqrt 3 / 2 ≤ z.im}) ∪
          ModularGroup.T⁻¹ • (modularStrip ∩ {z : ℍ | Real.sqrt 3 / 2 ≤ z.im})) :=
        measure_mono fd_subset_union_translate
    _ ≤ volume (modularStrip ∩ {z : ℍ | Real.sqrt 3 / 2 ≤ z.im}) +
          volume (ModularGroup.T⁻¹ • (modularStrip ∩ {z : ℍ | Real.sqrt 3 / 2 ≤ z.im})) :=
        measure_union_le _ _
    _ = volume (modularStrip ∩ {z : ℍ | Real.sqrt 3 / 2 ≤ z.im}) +
          volume (modularStrip ∩ {z : ℍ | Real.sqrt 3 / 2 ≤ z.im}) := by rw [measure_smul]
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hS, hS⟩

theorem volume_fd_ne_top : (volume : Measure ℍ) fd ≠ ∞ := volume_fd_lt_top.ne

/-! ## Open sets have positive volume -/

/-- The Lebesgue density of the invariant measure, written through `ofReal`. -/
theorem volume_eq_lintegral_ofReal (s : Set ℍ) :
    (volume : Measure ℍ) s = ∫⁻ z : ℂ in UpperHalfPlane.coe '' s, ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  rw [volume_eq_lintegral]
  refine lintegral_congr fun z => ?_
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, coe_nnnorm,
    Real.norm_eq_abs, one_div, inv_pow, sq_abs]

theorem measurable_ofReal_inv_im_sq :
    Measurable fun z : ℂ => ENNReal.ofReal ((z.im ^ 2)⁻¹) :=
  ((Complex.measurable_im.pow_const 2).inv).ennreal_ofReal

/-- **Every nonempty open subset of `ℍ` has positive volume.** -/
instance : (volume : Measure ℍ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [volume_eq_lintegral_ofReal]
  refine ((setLIntegral_pos_iff measurable_ofReal_inv_im_sq).mpr ?_).ne'
  have hopen : IsOpen (UpperHalfPlane.coe '' U) := isOpenEmbedding_coe.isOpenMap U hU
  have hsub : UpperHalfPlane.coe '' U ⊆
      Function.support (fun z : ℂ => ENNReal.ofReal ((z.im ^ 2)⁻¹)) := by
    rintro _ ⟨z, _, rfl⟩
    rw [Function.mem_support]
    have := z.im_pos
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  rw [inter_eq_self_of_subset_right hsub]
  exact hopen.measure_pos volume (hne.image _)

end

end GaloisForLFunctions.HTGeometry
