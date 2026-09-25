import GaloisForLFunctions.RHTower.GL3IwasawaGroup
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Block


/-!
# The measure `dx dy / (y₁y₂)³` is a Haar measure of the Iwasawa group `h³`

The measure on `h³` is Lebesgue measure on the coordinates `(x₁, x₂, x₃, y₁, y₂)` weighted by
`(y₁y₂)⁻³` (`volume_def`); in coordinates, `volume s = ∫_{coords s} (p₃p₄)⁻³ dp`
(`volume_eq_lintegral`).

Left translation `w ↦ z * w` is affine in coordinates with lower-triangular linear part of
diagonal `(y₁, y₂, y₁y₂, y₁, y₂)` (`coords_mul`, `transMat`), so its Jacobian is `(y₁y₂)³`
(`det_transMat`), which cancels the change of density; the change-of-variables formula gives
`volume_image_mul`. Together with local finiteness of a continuous density and positivity on open
sets, the measure is a Haar measure of the group `h³`.
-/

open Matrix Topology MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### The coordinate measure `dx dy / (y₁y₂)³` -/

theorem measurableEmbedding_coords : MeasurableEmbedding coords :=
  isOpenEmbedding_coords.measurableEmbedding

/-- The density `(y₁y₂)⁻³`. -/
noncomputable def dens (z : H3) : ℝ≥0 := Real.toNNReal ((z.y1 * z.y2) ^ 3)⁻¹

theorem continuous_dens : Continuous dens :=
  continuous_real_toNNReal.comp <|
    ((continuous_y1.mul continuous_y2).pow 3).inv₀ fun z => (pow_pos (mul_pos z.y1_pos z.y2_pos) 3).ne'

/-- **The invariant measure on `h³`**: `dx₁ dx₂ dx₃ dy₁ dy₂ / (y₁y₂)³`. -/
noncomputable instance : MeasureSpace H3 :=
  ⟨(volume.comap coords).withDensity fun z => (dens z : ℝ≥0∞)⟩

theorem volume_def :
    (volume : Measure H3) = (volume.comap coords).withDensity fun z => (dens z : ℝ≥0∞) := rfl

instance : IsFiniteMeasureOnCompacts (volume.comap coords) :=
  .comap' _ continuous_coords measurableEmbedding_coords

instance : IsLocallyFiniteMeasure (volume : Measure H3) :=
  .withDensity_coe continuous_dens

instance : IsFiniteMeasureOnCompacts (volume : Measure H3) := inferInstance

/-- The density in coordinates. -/
noncomputable def rho (p : Fin 5 → ℝ) : ℝ≥0∞ := ENNReal.ofReal ((p 3 * p 4) ^ 3)⁻¹

/-- The measure of a set as a Lebesgue integral of `(p₃p₄)⁻³` over its coordinate image. -/
theorem volume_eq_lintegral (s : Set H3) : volume s = ∫⁻ p in coords '' s, rho p := by
  have hmp : MeasurePreserving coords (volume.comap coords) (volume.restrict (Set.range coords)) :=
    ⟨measurableEmbedding_coords.measurable, by rw [measurableEmbedding_coords.map_comap]⟩
  rw [volume_def, withDensity_apply',
    ← Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _),
    ← Measure.restrict_restrict' measurableEmbedding_coords.measurableSet_range,
    ← hmp.setLIntegral_comp_emb measurableEmbedding_coords]
  refine lintegral_congr fun z => ?_
  simp [dens, rho, coords, ENNReal.ofReal]

theorem measurable_rho : Measurable rho := by
  unfold rho; fun_prop

theorem rho_ne_zero {p : Fin 5 → ℝ} (hp : p ∈ dom) : rho p ≠ 0 :=
  (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (mul_pos hp.1 hp.2) 3))).ne'

/-! ### Left translations in coordinates -/

/-- The linear part of left translation by `z` in Iwasawa coordinates. -/
def transMat (z : H3) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![z.y1, 0, 0, 0, 0; 0, z.y2, 0, 0, 0; z.y1 * z.x2, 0, z.y1 * z.y2, 0, 0; 0, 0, 0, z.y1, 0;
    0, 0, 0, 0, z.y2]

/-- Left translation by `z` in Iwasawa coordinates, an affine map. -/
def transAff (z : H3) (p : Fin 5 → ℝ) : Fin 5 → ℝ := ![z.x1, z.x2, z.x3, 0, 0] + transMat z *ᵥ p

theorem coords_mul (z w : H3) : coords (z * w) = transAff z (coords w) := by
  ext i
  fin_cases i <;>
    simp [coords, transAff, transMat] <;> ring

theorem det_transMat (z : H3) : (transMat z).det = (z.y1 * z.y2) ^ 3 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [transMat, Fin.prod_univ_five]
    ring
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp [transMat] at h ⊢
    all_goals exact absurd h (by decide)

/-- The derivative of `transAff z`. -/
noncomputable def transCLM (z : H3) : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (transMat z))

theorem hasFDerivAt_transAff (z : H3) (p : Fin 5 → ℝ) : HasFDerivAt (transAff z) (transCLM z) p := by
  have e : transAff z = fun p => ![z.x1, z.x2, z.x3, 0, 0] + transCLM z p := by
    funext p; simp [transAff, transCLM, Matrix.toLin'_apply]
  rw [e]
  exact (transCLM z).hasFDerivAt.const_add _

theorem det_transCLM (z : H3) : (transCLM z).det = (z.y1 * z.y2) ^ 3 := by
  rw [← det_transMat, ← LinearMap.det_toLin']
  rfl

/-- **Left translations preserve the coordinate measure**: the affine Jacobian `(y₁y₂)³` of
`w ↦ z * w` cancels the change of the density `(y₁y₂)⁻³`. -/
theorem volume_image_mul (z : H3) {s : Set H3} (hs : MeasurableSet s) :
    volume ((z * ·) '' s) = volume s := by
  rw [volume_eq_lintegral, volume_eq_lintegral]
  have himg : coords '' ((z * ·) '' s) = transAff z '' (coords '' s) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun w _ => coords_mul z w
  have hms : MeasurableSet (coords '' s) := measurableEmbedding_coords.measurableSet_image.2 hs
  have hinj : Set.InjOn (transAff z) (coords '' s) := by
    rintro _ ⟨w, -, rfl⟩ _ ⟨w', -, rfl⟩ h
    rw [← coords_mul, ← coords_mul] at h
    rw [mul_left_cancel (coords_injective h)]
  rw [himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hms
    (fun p _ => (hasFDerivAt_transAff z p).hasFDerivWithinAt) hinj rho]
  refine setLIntegral_congr_fun hms ?_
  rintro _ ⟨w, -, rfl⟩
  show ENNReal.ofReal |(transCLM z).det| * rho (transAff z (coords w)) = rho (coords w)
  rw [det_transCLM, ← coords_mul]
  have h1 := z.y1_pos; have h2 := z.y2_pos; have h3 := w.y1_pos; have h4 := w.y2_pos
  simp only [rho, coords, Matrix.cons_val, mul_y1, mul_y2]
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity)]
  congr 1
  field_simp

instance : (volume : Measure H3).IsMulLeftInvariant :=
  ⟨fun z => by
    ext A hA
    rw [Measure.map_apply (measurable_const_mul z) hA]
    have e : (fun w => z * w) ⁻¹' A = (fun w => z⁻¹ * w) '' A := by
      rw [Set.image_mul_left, inv_inv]
    rw [e, volume_image_mul z⁻¹ hA]⟩

instance : Measure.IsOpenPosMeasure (volume : Measure H3) where
  open_pos U hU hne := by
    rw [volume_eq_lintegral]
    intro h0
    have hmU : MeasurableSet (coords '' U) :=
      measurableEmbedding_coords.measurableSet_image.2 hU.measurableSet
    have hopen : IsOpen (coords '' U) := isOpenEmbedding_coords.isOpenMap U hU
    rw [setLIntegral_eq_zero_iff hmU measurable_rho] at h0
    have hnull : volume (coords '' U) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [h0] with p hp hpU
      obtain ⟨w, hw, rfl⟩ := hpU
      exact rho_ne_zero ⟨w.y1_pos, w.y2_pos⟩ (hp ⟨w, hw, rfl⟩)
    exact hopen.measure_ne_zero volume (hne.image coords) hnull

/-- **The coordinate measure is a Haar measure of the Iwasawa group `h³`.** -/
instance : (volume : Measure H3).IsHaarMeasure where

end H3
end GaloisForLFunctions.RHTower.GL3
