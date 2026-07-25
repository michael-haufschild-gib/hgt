import Mathlib

/-!
# The sum-difference change of variables

The substitution `u = w + t`, `v = w - t` used in the center-mixed Fourier computation is the linear
map `(w,t) ↦ (w+t, w-t)` of the plane, whose determinant is `-2`.  Consequently

`∫ H (w+t, w-t) dw dt = (1/2) ∫ H (u,v) du dv`.

This is the step that converts the density, which is an integral over a one-parameter family of
lines, into a genuine double integral over the plane, where the weight `u+v` factorises.
-/

open MeasureTheory

namespace HTGeometry

/-- The sum-difference substitution `(w,t) ↦ (w+t, w-t)` as a linear map of the plane. -/
def sumDiffMap : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1 + p.2, p.1 - p.2)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_eq_mul, RingHom.id_apply,
      Prod.mk.injEq]
    constructor <;> ring

@[simp] theorem sumDiffMap_apply (p : ℝ × ℝ) : sumDiffMap p = (p.1 + p.2, p.1 - p.2) := rfl

/-- The sum-difference substitution has determinant `-2`. -/
theorem det_sumDiffMap : LinearMap.det sumDiffMap = -2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.finTwoProd]
  norm_num

/-- **The sum-difference change of variables.**  Precomposing with `(w,t) ↦ (w+t, w-t)` multiplies
the integral by `1/2`. -/
theorem integral_comp_sumDiff (H : ℝ × ℝ → ℂ) (hH : Integrable H) :
    ∫ p : ℝ × ℝ, H (p.1 + p.2, p.1 - p.2) = (2 : ℝ)⁻¹ • ∫ p : ℝ × ℝ, H p := by
  have hdet : LinearMap.det sumDiffMap ≠ 0 := by
    rw [det_sumDiffMap]; norm_num
  have hmap : Measure.map (⇑sumDiffMap) (volume : Measure (ℝ × ℝ))
      = ENNReal.ofReal |(LinearMap.det sumDiffMap)⁻¹| • (volume : Measure (ℝ × ℝ)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ℝ × ℝ)) hdet
  have hmeas : AEMeasurable (⇑sumDiffMap) (volume : Measure (ℝ × ℝ)) :=
    (sumDiffMap.continuous_of_finiteDimensional).measurable.aemeasurable
  have hcomp : ∫ q : ℝ × ℝ, H q ∂(Measure.map (⇑sumDiffMap) volume)
      = ∫ p : ℝ × ℝ, H (sumDiffMap p) := by
    refine integral_map hmeas ?_
    rw [hmap]
    exact (hH.aestronglyMeasurable).smul_measure _
  rw [hmap] at hcomp
  simp only [sumDiffMap_apply] at hcomp
  rw [← hcomp, integral_smul_measure, det_sumDiffMap]
  congr 1
  rw [show |((-2 : ℝ))⁻¹| = (2 : ℝ)⁻¹ by rw [abs_of_nonpos] <;> norm_num]
  simp

end HTGeometry
