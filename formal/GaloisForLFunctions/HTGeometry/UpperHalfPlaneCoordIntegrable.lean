import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral

open UpperHalfPlane MeasureTheory Set Filter
open scoped NNReal ENNReal

/-!
# Integrability on the upper half-plane in coordinates

For a measurable set `A` of pairs `(x, y)` with `y > 0`, a function `F` on `ℍ` is integrable for the invariant measure
`dx dy / y²` on `{z | (Re z, Im z) ∈ A}` iff `(x, y) ↦ F(x + iy) / y²` is Lebesgue integrable on `A`
(`integrableOn_coord_iff`).
-/

namespace GaloisForLFunctions.HTGeometry.UpperHalfPlaneCoordIntegrable
open GaloisForLFunctions.HTGeometry

/-- **Integrability in coordinates.** For measurable `A ⊆ {p.2 > 0}`, `F` is integrable on `{z | (Re z, Im z) ∈ A}`
iff `p ↦ F(p.1 + i p.2) / p.2²` is integrable on `A`. -/
theorem integrableOn_coord_iff {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hpos : ∀ p ∈ A, 0 < p.2)
    (F : ℍ → ℂ) :
    IntegrableOn F {z : ℍ | (z.re, z.im) ∈ A} volume ↔
      IntegrableOn (fun p : ℝ × ℝ => F (ofComplex ⟨p.1, p.2⟩) / ((p.2 : ℝ) : ℂ) ^ 2) A volume := by
  set S : Set ℍ := {z : ℍ | (z.re, z.im) ∈ A}
  have hS : MeasurableSet S :=
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im).measurable hA
  rw [IntegrableOn, volume_eq_comap_withDensity, restrict_withDensity hS,
    integrable_withDensity_iff_integrable_smul' measurable_hyperbolicDensity
      (ae_of_all _ fun z => hyperbolicDensity_lt_top z)]
  show IntegrableOn (fun z => (hyperbolicDensity z).toReal • F z) S (volume.comap UpperHalfPlane.coe) ↔ _
  have h2 := measurePreserving_coe.integrableOn_image measurableEmbedding_coe
    (f := fun w => (hyperbolicDensity (ofComplex w)).toReal • F (ofComplex w)) (s := S)
  simp only [Function.comp_def, ofComplex_apply] at h2
  rw [← h2]
  have hSc : MeasurableSet (UpperHalfPlane.coe '' S) := measurableEmbedding_coe.measurableSet_image.mpr hS
  have hres : (volume.restrict (range UpperHalfPlane.coe)).restrict (UpperHalfPlane.coe '' S) =
      (volume : Measure ℂ).restrict (UpperHalfPlane.coe '' S) := by
    rw [Measure.restrict_restrict hSc, inter_eq_self_of_subset_left (image_subset_range _ _)]
  rw [IntegrableOn, hres, ← IntegrableOn]
  have h3 := Complex.volume_preserving_equiv_real_prod.integrableOn_image
    Complex.measurableEquivRealProd.measurableEmbedding
    (f := fun p : ℝ × ℝ => (hyperbolicDensity (ofComplex ⟨p.1, p.2⟩)).toReal • F (ofComplex ⟨p.1, p.2⟩))
    (s := UpperHalfPlane.coe '' S)
  have himg : Complex.measurableEquivRealProd '' (UpperHalfPlane.coe '' S) = A := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨w, ⟨z, hz, rfl⟩, hw⟩
      simp only [Complex.measurableEquivRealProd_apply] at hw
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
      exact hz
    · intro hp
      have hy : 0 < y := hpos _ hp
      refine ⟨⟨x, y⟩, ⟨⟨⟨x, y⟩, hy⟩, hp, rfl⟩, rfl⟩
  rw [himg] at h3
  simp only [Function.comp_def, Complex.measurableEquivRealProd_apply] at h3
  have e1 : ∀ w : ℂ, (⟨w.re, w.im⟩ : ℂ) = w := fun w => Complex.ext rfl rfl
  simp only [e1] at h3
  rw [← h3]
  constructor
  · intro h
    refine h.congr_fun (fun p hp => (?_ : _ = _).symm) hA
    have hy : 0 < p.2 := hpos p hp
    have him : (ofComplex (⟨p.1, p.2⟩ : ℂ)).im = p.2 := by
      rw [ofComplex_apply_of_im_pos (by simpa using hy)]; rfl
    simp only
    rw [hyperbolicDensity_toReal, him, Complex.real_smul]
    have hy2 : ((p.2 : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hy.ne')
    push_cast
    field_simp
  · intro h
    refine h.congr_fun (fun p hp => ?_) hA
    have hy : 0 < p.2 := hpos p hp
    have him : (ofComplex (⟨p.1, p.2⟩ : ℂ)).im = p.2 := by
      rw [ofComplex_apply_of_im_pos (by simpa using hy)]; rfl
    simp only
    rw [hyperbolicDensity_toReal, him, Complex.real_smul]
    have hy2 : ((p.2 : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hy.ne')
    push_cast
    field_simp

end GaloisForLFunctions.HTGeometry.UpperHalfPlaneCoordIntegrable
