import GaloisForLFunctions.HTGeometry.ModularStripUnfolding
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals over the strip `0 ≤ Re z < 1` of the upper half-plane

The invariant measure `dx dy / y²` on `ℍ` is the Lebesgue measure of `ℂ` restricted to `ℍ` with the
density `y⁻²`.  Through the chart `(y, x) ↦ x + iy` an integral over the strip
`{0 ≤ Re z < 1}` becomes an integral over `(0, ∞) × [0, 1)` against Lebesgue measure,

  `∫_{strip} F dμ = ∫_{(0,∞) × [0,1)} y⁻² F(x + iy) d(y, x)`,

and integrability on the strip is equivalent to integrability of `y⁻² F(x + iy)` on the product.
Fubini then turns the right-hand side into the iterated integral
`∫_0^∞ y⁻² (∫_0^1 F(x + iy) dx) dy`.
-/

open UpperHalfPlane MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The hyperbolic density -/

/-- The density `y⁻²` of the invariant measure with respect to Lebesgue measure. -/
def hyperbolicDensity (z : ℍ) : ℝ≥0∞ := ENNReal.ofReal ((z.im ^ 2)⁻¹)

theorem measurable_hyperbolicDensity : Measurable hyperbolicDensity :=
  ((continuous_im.measurable.pow_const 2).inv).ennreal_ofReal

theorem hyperbolicDensity_lt_top (z : ℍ) : hyperbolicDensity z < ∞ := ENNReal.ofReal_lt_top

theorem hyperbolicDensity_toReal (z : ℍ) : (hyperbolicDensity z).toReal = (z.im ^ 2)⁻¹ :=
  ENNReal.toReal_ofReal (by positivity)

/-- The invariant measure is Lebesgue measure on `ℍ ⊆ ℂ` with density `y⁻²`. -/
theorem volume_eq_comap_withDensity :
    (volume : Measure ℍ) = (volume.comap UpperHalfPlane.coe).withDensity hyperbolicDensity := by
  rw [volume_def]
  congr 1
  funext z
  rw [hyperbolicDensity, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_mk, one_div, inv_pow]

/-! ## The chart `(y, x) ↦ x + iy` -/

/-- The measurable equivalence `ℂ ≃ ℝ × ℝ`, `w ↦ (Im w, Re w)`. -/
def stripEquiv : ℂ ≃ᵐ ℝ × ℝ := Complex.measurableEquivRealProd.trans MeasurableEquiv.prodComm

theorem stripEquiv_apply (w : ℂ) : stripEquiv w = (w.im, w.re) := rfl

theorem stripEquiv_symm_apply (p : ℝ × ℝ) : stripEquiv.symm p = ⟨p.2, p.1⟩ := rfl

theorem measurePreserving_stripEquiv : MeasurePreserving stripEquiv volume volume := by
  refine Complex.volume_preserving_equiv_real_prod.trans ?_
  rw [Measure.volume_eq_prod]
  exact Measure.measurePreserving_swap

/-- The strip in the chart is `(0, ∞) × [0, 1)`. -/
theorem stripEquiv_image_coe_modularStrip :
    stripEquiv '' (UpperHalfPlane.coe '' modularStrip) = Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1 := by
  ext ⟨y, x⟩
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, hw⟩
    rw [stripEquiv_apply] at hw
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
    exact ⟨z.im_pos, hz⟩
  · rintro ⟨hy, hx⟩
    exact ⟨⟨x, y⟩, ⟨⟨⟨x, y⟩, hy⟩, hx, rfl⟩, rfl⟩

/-! ## Transport from the strip to the chart -/

/-- Lebesgue measure on `ℍ ⊆ ℂ` is the pushforward of the comap. -/
theorem measurePreserving_coe :
    MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
  ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩

theorem measurableSet_coe_image_modularStrip :
    MeasurableSet (UpperHalfPlane.coe '' modularStrip) :=
  measurableEmbedding_coe.measurableSet_image.mpr measurableSet_modularStrip

theorem restrict_range_restrict_coe_image_modularStrip :
    (volume.restrict (range UpperHalfPlane.coe)).restrict (UpperHalfPlane.coe '' modularStrip)
      = (volume : Measure ℂ).restrict (UpperHalfPlane.coe '' modularStrip) := by
  rw [Measure.restrict_restrict measurableSet_coe_image_modularStrip,
    inter_eq_self_of_subset_left (image_subset_range _ _)]

theorem integrableOn_coe_image_modularStrip_restrict_range_iff (f : ℂ → ℂ) :
    IntegrableOn f (UpperHalfPlane.coe '' modularStrip) (volume.restrict (range UpperHalfPlane.coe))
      ↔ IntegrableOn f (UpperHalfPlane.coe '' modularStrip) volume := by
  rw [IntegrableOn, IntegrableOn, restrict_range_restrict_coe_image_modularStrip]

/-- The chart integrand: `y⁻² F(x + iy)` at `p = (y, x)`. -/
def stripChartIntegrand (F : ℍ → ℂ) (p : ℝ × ℝ) : ℂ := (p.1 ^ 2)⁻¹ • F (ofComplex ⟨p.2, p.1⟩)

theorem stripChartIntegrand_eq_on (F : ℍ → ℂ) {p : ℝ × ℝ}
    (hp : p ∈ Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) :
    (hyperbolicDensity (ofComplex (stripEquiv.symm p))).toReal • F (ofComplex (stripEquiv.symm p))
      = stripChartIntegrand F p := by
  have hy : (0 : ℝ) < p.1 := hp.1
  have him : (ofComplex (⟨p.2, p.1⟩ : ℂ)).im = p.1 := by
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  rw [stripEquiv_symm_apply, hyperbolicDensity_toReal, him, stripChartIntegrand]

/-- **The strip integral in the chart.** -/
theorem setIntegral_modularStrip_eq_chart (F : ℍ → ℂ) :
    ∫ z in modularStrip, F z
      = ∫ p in Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1, stripChartIntegrand F p := by
  rw [volume_eq_comap_withDensity,
    setIntegral_withDensity_eq_setIntegral_toReal_smul measurable_hyperbolicDensity
      (ae_of_all _ fun z => hyperbolicDensity_lt_top z) F measurableSet_modularStrip]
  have h2 := measurePreserving_coe.setIntegral_image_emb measurableEmbedding_coe
    (fun w => (hyperbolicDensity (ofComplex w)).toReal • F (ofComplex w)) modularStrip
  simp only [ofComplex_apply] at h2
  rw [← h2, restrict_range_restrict_coe_image_modularStrip]
  have h3 := measurePreserving_stripEquiv.setIntegral_image_emb stripEquiv.measurableEmbedding
    (fun p => (hyperbolicDensity (ofComplex (stripEquiv.symm p))).toReal •
      F (ofComplex (stripEquiv.symm p))) (UpperHalfPlane.coe '' modularStrip)
  simp only [MeasurableEquiv.symm_apply_apply] at h3
  rw [← h3, stripEquiv_image_coe_modularStrip]
  exact setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ico)
    fun p hp => stripChartIntegrand_eq_on F hp

/-- **Integrability on the strip** is integrability of the chart integrand on `(0,∞) × [0,1)`. -/
theorem integrableOn_modularStrip_iff (F : ℍ → ℂ) :
    IntegrableOn F modularStrip volume
      ↔ IntegrableOn (stripChartIntegrand F) (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) volume := by
  rw [IntegrableOn, volume_eq_comap_withDensity, restrict_withDensity measurableSet_modularStrip,
    integrable_withDensity_iff_integrable_smul' measurable_hyperbolicDensity
      (ae_of_all _ fun z => hyperbolicDensity_lt_top z)]
  show IntegrableOn (fun z => (hyperbolicDensity z).toReal • F z) modularStrip
    (volume.comap UpperHalfPlane.coe) ↔ _
  have h2 := measurePreserving_coe.integrableOn_image measurableEmbedding_coe
    (f := fun w => (hyperbolicDensity (ofComplex w)).toReal • F (ofComplex w)) (s := modularStrip)
  simp only [Function.comp_def, ofComplex_apply] at h2
  rw [← h2, integrableOn_coe_image_modularStrip_restrict_range_iff]
  have h3 := measurePreserving_stripEquiv.integrableOn_image stripEquiv.measurableEmbedding
    (f := fun p => (hyperbolicDensity (ofComplex (stripEquiv.symm p))).toReal •
      F (ofComplex (stripEquiv.symm p))) (s := UpperHalfPlane.coe '' modularStrip)
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply] at h3
  rw [← h3, stripEquiv_image_coe_modularStrip]
  constructor
  · intro h
    exact h.congr_fun (fun p hp => stripChartIntegrand_eq_on F hp)
      (measurableSet_Ioi.prod measurableSet_Ico)
  · intro h
    exact h.congr_fun (fun p hp => (stripChartIntegrand_eq_on F hp).symm)
      (measurableSet_Ioi.prod measurableSet_Ico)

/-! ## The iterated form -/

/-- **Fubini on the strip**: `∫_{strip} F = ∫_0^∞ y⁻² (∫_0^1 F(x + iy) dx) dy`. -/
theorem setIntegral_modularStrip_eq_iterated (F : ℍ → ℂ) (hF : IntegrableOn F modularStrip volume) :
    ∫ z in modularStrip, F z
      = ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ • ∫ x in Ico (0 : ℝ) 1, F (ofComplex ⟨x, y⟩) := by
  rw [setIntegral_modularStrip_eq_chart, Measure.volume_eq_prod,
    setIntegral_prod _ ((integrableOn_modularStrip_iff F).mp hF)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  simp only [stripChartIntegrand]
  rw [integral_smul]

end

end GaloisForLFunctions.HTGeometry
