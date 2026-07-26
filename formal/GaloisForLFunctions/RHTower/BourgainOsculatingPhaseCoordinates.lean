/-
# Literal osculating phase coordinates

Bourgain (1.23)--(1.24) uses

`x ↦ (x·Φ'(a²), ½ x·Φ''(a²), x·Φ'(b²), ½ x·Φ''(b²))`.

The derivative matrix in `BourgainSquareRootOsculatingGeometry` stores the
jets as columns.  The actual phase-coordinate map is therefore its transpose,
with the second-derivative rows scaled by `1/2`.  This module records that
literal matrix and its exact determinant, including both missing half
factors.
-/
import GaloisForLFunctions.RHTower.BourgainSquareRootOsculatingGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000

/-- Literal coordinate matrix for
`(x·Φ'(a²), ½x·Φ''(a²), x·Φ'(b²), ½x·Φ''(b²))`. -/
def bourgainSquareRootPhaseCoordinateMatrix
    (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 2 * a ^ 2, 3 * a / 2, 1 / (2 * a);
     0, 1, 3 / (8 * a), -1 / (8 * a ^ 3);
     1, 2 * b ^ 2, 3 * b / 2, 1 / (2 * b);
     0, 1, 3 / (8 * b), -1 / (8 * b ^ 3)]

/-- Applying the literal coordinate matrix. -/
def bourgainSquareRootPhaseCoordinates
    (a b : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  (bourgainSquareRootPhaseCoordinateMatrix a b).mulVec x

@[simp] theorem bourgainSquareRootPhaseCoordinates_zero
    (a b : ℝ) (x : Fin 4 → ℝ) :
    bourgainSquareRootPhaseCoordinates a b x 0 =
      x 0 + 2 * a ^ 2 * x 1 + (3 * a / 2) * x 2 +
        (1 / (2 * a)) * x 3 := by
  simp [bourgainSquareRootPhaseCoordinates,
    bourgainSquareRootPhaseCoordinateMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four]

@[simp] theorem bourgainSquareRootPhaseCoordinates_one
    (a b : ℝ) (x : Fin 4 → ℝ) :
    bourgainSquareRootPhaseCoordinates a b x 1 =
      x 1 + (3 / (8 * a)) * x 2 - (1 / (8 * a ^ 3)) * x 3 := by
  simp [bourgainSquareRootPhaseCoordinates,
    bourgainSquareRootPhaseCoordinateMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four]
  ring

@[simp] theorem bourgainSquareRootPhaseCoordinates_two
    (a b : ℝ) (x : Fin 4 → ℝ) :
    bourgainSquareRootPhaseCoordinates a b x 2 =
      x 0 + 2 * b ^ 2 * x 1 + (3 * b / 2) * x 2 +
        (1 / (2 * b)) * x 3 := by
  simp [bourgainSquareRootPhaseCoordinates,
    bourgainSquareRootPhaseCoordinateMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four]

@[simp] theorem bourgainSquareRootPhaseCoordinates_three
    (a b : ℝ) (x : Fin 4 → ℝ) :
    bourgainSquareRootPhaseCoordinates a b x 3 =
      x 1 + (3 / (8 * b)) * x 2 - (1 / (8 * b ^ 3)) * x 3 := by
  simp [bourgainSquareRootPhaseCoordinates,
    bourgainSquareRootPhaseCoordinateMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four]
  ring

/-- Exact determinant of the literal phase-coordinate map.  Relative to the
unscaled derivative matrix, the two `1/2` factors divide the determinant by
four. -/
theorem det_bourgainSquareRootPhaseCoordinateMatrix
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (bourgainSquareRootPhaseCoordinateMatrix a b).det =
      3 * (b - a) ^ (4 : ℕ) /
        (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)) := by
  have h21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [Matrix.det_succ_row_zero]
  simp [bourgainSquareRootPhaseCoordinateMatrix, Matrix.det_fin_three,
    Fin.sum_univ_four, h21, h22, h12, h31, h32]
  field_simp
  ring

/-- Positivity for separated positive square-root parameters. -/
theorem det_bourgainSquareRootPhaseCoordinateMatrix_pos
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < (bourgainSquareRootPhaseCoordinateMatrix a b).det := by
  rw [det_bourgainSquareRootPhaseCoordinateMatrix ha.ne'
    (lt_trans ha hab).ne']
  exact div_pos
    (mul_pos (by norm_num) (pow_pos (sub_pos.mpr hab) 4))
    (mul_pos (mul_pos (by norm_num) (pow_pos ha 3))
      (pow_pos (lt_trans ha hab) 3))

/-- The literal phase-coordinate matrix is a unit. -/
theorem isUnit_bourgainSquareRootPhaseCoordinateMatrix
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsUnit (bourgainSquareRootPhaseCoordinateMatrix a b) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact ne_of_gt
    (det_bourgainSquareRootPhaseCoordinateMatrix_pos ha hab)

/-- Linear equivalence implementing the literal coordinate change in
(1.23)--(1.24). -/
noncomputable def bourgainSquareRootPhaseCoordinateLinearEquiv
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofBijective
    (bourgainSquareRootPhaseCoordinateMatrix a b).mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr
        (isUnit_bourgainSquareRootPhaseCoordinateMatrix ha hab),
      Matrix.mulVec_surjective_iff_isUnit.mpr
        (isUnit_bourgainSquareRootPhaseCoordinateMatrix ha hab)⟩

/-- Continuous linear equivalence for the literal phase coordinates. -/
noncomputable def bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ) :=
  (bourgainSquareRootPhaseCoordinateLinearEquiv ha hab).toContinuousLinearEquiv

@[simp] theorem bourgainSquareRootPhaseCoordinateContinuousLinearEquiv_apply
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : Fin 4 → ℝ) :
    bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab x =
      bourgainSquareRootPhaseCoordinates a b x := by
  rfl

/-- Operator-norm containment of an original physical cube in a phase-
coordinate cube. -/
theorem norm_bourgainSquareRootPhaseCoordinates_le
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : Fin 4 → ℝ) :
    ‖bourgainSquareRootPhaseCoordinates a b x‖ ≤
      ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ *
        ‖x‖ := by
  simpa using
    (bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab :
      (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)).le_opNorm x

/-- The inverse operator norm supplies the complementary lower distortion
bound. -/
theorem norm_le_inverseNorm_mul_norm_bourgainSquareRootPhaseCoordinates
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : Fin 4 → ℝ) :
    ‖x‖ ≤
      ‖((bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab).symm :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ *
        ‖bourgainSquareRootPhaseCoordinates a b x‖ := by
  have h :=
    ((bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab).symm :
      (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)).le_opNorm
        (bourgainSquareRootPhaseCoordinates a b x)
  calc
    ‖x‖ =
        ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab).symm
          (bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab x)‖ := by
            rw [ContinuousLinearEquiv.symm_apply_apply]
    _ =
        ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab).symm
          (bourgainSquareRootPhaseCoordinates a b x)‖ := by
            rw [bourgainSquareRootPhaseCoordinateContinuousLinearEquiv_apply]
    _ ≤
        ‖((bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab).symm :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ *
          ‖bourgainSquareRootPhaseCoordinates a b x‖ := h

/-- Exact Lebesgue Jacobian of the literal phase-coordinate map. -/
theorem map_bourgainSquareRootPhaseCoordinateMatrix_volume
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.Measure.map
        (Matrix.toLin' (bourgainSquareRootPhaseCoordinateMatrix a b))
        MeasureTheory.volume =
      ENNReal.ofReal
          |(3 * (b - a) ^ (4 : ℕ) /
            (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| •
        MeasureTheory.volume := by
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi
    (ne_of_gt
      (det_bourgainSquareRootPhaseCoordinateMatrix_pos ha hab))]
  rw [det_bourgainSquareRootPhaseCoordinateMatrix ha.ne'
    (lt_trans ha hab).ne']

/-- Exact global change-of-variables identity for real-valued phase-space
integrands. -/
theorem integral_comp_bourgainSquareRootPhaseCoordinates
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (f : (Fin 4 → ℝ) → ℝ)
    (hf : MeasureTheory.StronglyMeasurable f) :
    (∫ x, f (bourgainSquareRootPhaseCoordinates a b x)) =
      (ENNReal.ofReal
          |(3 * (b - a) ^ (4 : ℕ) /
            (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹|).toReal *
        ∫ y, f y := by
  let M := bourgainSquareRootPhaseCoordinateMatrix a b
  have hM : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  calc
    (∫ x, f (bourgainSquareRootPhaseCoordinates a b x)) =
        ∫ x, f (Matrix.toLin' M x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [Matrix.toLin'_apply]
          rfl
    _ = ∫ y, f y ∂MeasureTheory.Measure.map (Matrix.toLin' M)
          MeasureTheory.volume := by
          symm
          exact MeasureTheory.integral_map_of_stronglyMeasurable hM hf
    _ = ∫ y, f y ∂
          (ENNReal.ofReal
              |(3 * (b - a) ^ (4 : ℕ) /
                (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| •
            MeasureTheory.volume) := by
          rw [show Matrix.toLin' M =
              Matrix.toLin' (bourgainSquareRootPhaseCoordinateMatrix a b) by
                rfl,
            map_bourgainSquareRootPhaseCoordinateMatrix_volume ha hab]
    _ =
        (ENNReal.ofReal
          |(3 * (b - a) ^ (4 : ℕ) /
            (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹|).toReal *
          ∫ y, f y := by
          rw [MeasureTheory.integral_smul_measure]
          rfl

/-- Localized nonnegative change of variables: a norm cube of radius `N`
maps inside the phase-coordinate norm cube enlarged by the operator norm,
with the exact Jacobian factor. -/
theorem setLIntegral_comp_bourgainSquareRootPhaseCoordinates_le
    {a b N : ℝ} (ha : 0 < a) (hab : a < b)
    (g : (Fin 4 → ℝ) → ENNReal) (hg : Measurable g) :
    (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        g (bourgainSquareRootPhaseCoordinates a b x)) ≤
      ENNReal.ofReal
          |(3 * (b - a) ^ (4 : ℕ) /
            (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| *
        ∫⁻ y in
          {y : Fin 4 → ℝ |
            ‖y‖ ≤
              ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab :
                (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * N},
          g y := by
  let M := bourgainSquareRootPhaseCoordinateMatrix a b
  let C : ℝ :=
    ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab :
      (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖
  let A : Set (Fin 4 → ℝ) := {x | ‖x‖ ≤ N}
  let B : Set (Fin 4 → ℝ) := {y | ‖y‖ ≤ C * N}
  have hA : MeasurableSet A := by
    exact measurableSet_Iic.preimage
      ((continuous_norm.comp continuous_id).measurable)
  have hB : MeasurableSet B := by
    exact measurableSet_Iic.preimage
      ((continuous_norm.comp continuous_id).measurable)
  have hM : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hcoord (x : Fin 4 → ℝ) :
      Matrix.toLin' M x = bourgainSquareRootPhaseCoordinates a b x := by
    rw [Matrix.toLin'_apply]
    rfl
  have hsubset : A ⊆ (Matrix.toLin' M) ⁻¹' B := by
    intro x hx
    change ‖Matrix.toLin' M x‖ ≤ C * N
    rw [hcoord]
    exact (norm_bourgainSquareRootPhaseCoordinates_le ha hab x).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  change
    (∫⁻ x in A, g (bourgainSquareRootPhaseCoordinates a b x)) ≤
      ENNReal.ofReal
          |(3 * (b - a) ^ (4 : ℕ) /
            (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| *
        ∫⁻ y in B, g y
  calc
    (∫⁻ x in A, g (bourgainSquareRootPhaseCoordinates a b x)) =
        ∫⁻ x in A, g (Matrix.toLin' M x) := by
          apply MeasureTheory.lintegral_congr
          intro x
          rw [hcoord]
    _ ≤ ∫⁻ x in (Matrix.toLin' M) ⁻¹' B,
          g (Matrix.toLin' M x) :=
      MeasureTheory.lintegral_mono_set hsubset
    _ = ∫⁻ y in B, g y ∂
          MeasureTheory.Measure.map (Matrix.toLin' M)
            MeasureTheory.volume := by
          symm
          exact MeasureTheory.setLIntegral_map hB hg hM
    _ = ∫⁻ y in B, g y ∂
          (ENNReal.ofReal
              |(3 * (b - a) ^ (4 : ℕ) /
                (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| •
            MeasureTheory.volume) := by
          rw [show Matrix.toLin' M =
              Matrix.toLin' (bourgainSquareRootPhaseCoordinateMatrix a b) by
                rfl,
            map_bourgainSquareRootPhaseCoordinateMatrix_volume ha hab]
    _ =
        ENNReal.ofReal
            |(3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| *
          ∫⁻ y in B, g y := by
          rw [MeasureTheory.setLIntegral_smul_measure]
          rfl

end

end RHTower
