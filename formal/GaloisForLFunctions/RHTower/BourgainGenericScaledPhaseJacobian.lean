/-
# Jacobian of generic scaled osculating coordinates

This module supplies the matrix and exact Lebesgue Jacobian for the generic
two-base jet map followed by Bourgain's anisotropic parabola dilation.
-/
import GaloisForLFunctions.RHTower.BourgainNormalizedCubeDecoupling

open MeasureTheory

namespace RHTower

noncomputable section

/-- Matrix of generic jet coordinates followed by parabola scaling. -/
def bourgainGenericScaledPhaseMatrix
    (φ₃ φ₄ : ℝ → ℝ) (scale a b : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  bourgainParabolaPhaseScaleMatrix scale *
    bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b

theorem bourgainGenericScaledPhaseMatrix_mulVec
    (φ₃ φ₄ : ℝ → ℝ) (scale a b : ℝ)
    (x : BourgainPhaseSpace) :
    (bourgainGenericScaledPhaseMatrix
        φ₃ φ₄ scale a b).mulVec x =
      bourgainGenericScaledPhaseCoordinates
        φ₃ φ₄ scale a b x := by
  unfold bourgainGenericScaledPhaseMatrix
    bourgainGenericScaledPhaseCoordinates
    bourgainGenericPhaseCoordinates
  rw [← Matrix.mulVec_mulVec,
    bourgainParabolaPhaseScaleMatrix_mulVec]

/-- Exact determinant of the combined generic scaled map. -/
theorem det_bourgainGenericScaledPhaseMatrix
    (φ₃ φ₄ : ℝ → ℝ) (scale a b : ℝ) :
    (bourgainGenericScaledPhaseMatrix φ₃ φ₄ scale a b).det =
      scale ^ (6 : ℕ) *
        (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).det := by
  unfold bourgainGenericScaledPhaseMatrix
  rw [Matrix.det_mul, det_bourgainParabolaPhaseScaleMatrix]

theorem isUnit_bourgainGenericScaledPhaseMatrix
    (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b)) :
    IsUnit (bourgainGenericScaledPhaseMatrix φ₃ φ₄ scale a b) := by
  rw [Matrix.isUnit_iff_isUnit_det,
    det_bourgainGenericScaledPhaseMatrix]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 6 hscale)).mul
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- Lebesgue measure under the combined generic scaled phase matrix. -/
theorem map_bourgainGenericScaledPhaseMatrix_volume
    (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b)) :
    Measure.map
        (Matrix.toLin'
          (bourgainGenericScaledPhaseMatrix φ₃ φ₄ scale a b))
        volume =
      ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).det)⁻¹| •
        volume := by
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi
    (by
      rw [det_bourgainGenericScaledPhaseMatrix]
      exact mul_ne_zero (pow_ne_zero 6 hscale)
        ((Matrix.isUnit_iff_isUnit_det _).mp hunit |>
          (isUnit_iff_ne_zero.mp)))]
  rw [det_bourgainGenericScaledPhaseMatrix]

/-- Pullback of the sharp independent-parabola period cell through generic
scaled osculating coordinates. -/
def bourgainGenericOsculatingFundamentalCell
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (scale a b : ℝ) :
    Set BourgainPhaseSpace :=
  {x |
    bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b x ∈
      bourgainParabolaFundamentalCell H}

theorem measurableSet_bourgainGenericOsculatingFundamentalCell
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b)) :
    MeasurableSet
      (bourgainGenericOsculatingFundamentalCell
        H φ₃ φ₄ scale a b) := by
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit
  have hE :
      (fun x : BourgainPhaseSpace =>
        bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b x) = E := by
    funext x
    exact
      (bourgainGenericScaledPhaseContinuousLinearEquiv_apply
        φ₃ φ₄ hscale hunit x).symm
  unfold bourgainGenericOsculatingFundamentalCell
  change MeasurableSet
    ((fun x : BourgainPhaseSpace =>
      bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b x) ⁻¹'
        bourgainParabolaFundamentalCell H)
  rw [hE]
  exact measurableSet_bourgainParabolaFundamentalCell H
    |>.preimage E.continuous.measurable

/-- Exact nonnegative change of variables on one generic pulled-back period
cell. -/
theorem setLIntegral_bourgainGenericOsculatingFundamentalCell_eq
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (f : BourgainPhaseSpace → ENNReal) (hf : Measurable f) :
    (∫⁻ x in bourgainGenericOsculatingFundamentalCell
        H φ₃ φ₄ scale a b, f x) =
      ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).det)⁻¹| *
        ∫⁻ y in bourgainParabolaFundamentalCell H,
          f ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm y) := by
  let M := bourgainGenericScaledPhaseMatrix φ₃ φ₄ scale a b
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit
  let g : BourgainPhaseSpace → ENNReal := fun y => f (E.symm y)
  have hM : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hg : Measurable g :=
    hf.comp E.symm.continuous.measurable
  have hcell := measurableSet_bourgainParabolaFundamentalCell H
  have hcoord (x : BourgainPhaseSpace) :
      Matrix.toLin' M x = E x := by
    rw [Matrix.toLin'_apply]
    exact
      (bourgainGenericScaledPhaseMatrix_mulVec
        φ₃ φ₄ scale a b x).trans
        (bourgainGenericScaledPhaseContinuousLinearEquiv_apply
          φ₃ φ₄ hscale hunit x).symm
  have hset :
      bourgainGenericOsculatingFundamentalCell
          H φ₃ φ₄ scale a b =
        (Matrix.toLin' M) ⁻¹' bourgainParabolaFundamentalCell H := by
    ext x
    simp only [bourgainGenericOsculatingFundamentalCell, Set.mem_preimage]
    rw [hcoord]
    exact
      bourgainGenericScaledPhaseContinuousLinearEquiv_apply
        φ₃ φ₄ hscale hunit x |>.symm ▸ Iff.rfl
  have hcomp :
      (fun x : BourgainPhaseSpace => g (Matrix.toLin' M x)) = f := by
    funext x
    dsimp [g]
    change f (E.symm (Matrix.toLin' M x)) = f x
    rw [hcoord, ContinuousLinearEquiv.symm_apply_apply]
  calc
    (∫⁻ x in bourgainGenericOsculatingFundamentalCell
        H φ₃ φ₄ scale a b, f x) =
        ∫⁻ x in (Matrix.toLin' M) ⁻¹'
            bourgainParabolaFundamentalCell H,
          g (Matrix.toLin' M x) := by
      rw [hset, hcomp]
    _ = ∫⁻ y in bourgainParabolaFundamentalCell H, g y ∂
          Measure.map (Matrix.toLin' M) volume := by
      symm
      exact setLIntegral_map hcell hg hM
    _ = ∫⁻ y in bourgainParabolaFundamentalCell H, g y ∂
          (ENNReal.ofReal
              |(scale ^ (6 : ℕ) *
                (bourgainGenericPhaseCoordinateMatrix
                  φ₃ φ₄ a b).det)⁻¹| • volume) := by
      dsimp [M]
      rw [map_bourgainGenericScaledPhaseMatrix_volume
        φ₃ φ₄ hscale hunit]
    _ = ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).det)⁻¹| *
        ∫⁻ y in bourgainParabolaFundamentalCell H, g y := by
      rw [setLIntegral_smul_measure]
      rfl
    _ = _ := by rfl

end

end RHTower
