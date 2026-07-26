/-
# Anisotropic fundamental cell in osculating coordinates

Bourgain's Section 2 uses the periods `H,H²,H,H²`, whose product is `H⁶`.
This module defines that exact cell and pulls it back through the combined
osculating-coordinate and parabola-dilation map.  Both Jacobians and the
sharp cell volume are retained exactly.
-/
import GaloisForLFunctions.RHTower.BourgainParabolaFundamentalCell
import GaloisForLFunctions.RHTower.BourgainA6FirstSpacingBridge
import GaloisForLFunctions.RHTower.BourgainAnisotropicPlanarTransfer

open MeasureTheory

namespace RHTower

noncomputable section

/-- Half-widths of one centered physical period cell. -/
def bourgainParabolaFundamentalHalfWidth
    (H : ℕ) : BourgainPhaseSpace :=
  ![(H : ℝ) / 2, (H : ℝ) ^ (2 : ℕ) / 2,
    (H : ℝ) / 2, (H : ℝ) ^ (2 : ℕ) / 2]

/-- Centered fundamental period cell with side lengths `H,H²,H,H²`. -/
def bourgainParabolaFundamentalCell
    (H : ℕ) : Set BourgainPhaseSpace :=
  bourgainFullBox (bourgainParabolaFundamentalHalfWidth H)

theorem measurableSet_bourgainParabolaFundamentalCell
    (H : ℕ) :
    MeasurableSet (bourgainParabolaFundamentalCell H) := by
  exact measurableSet_bourgainFullBox _

/-- Exact volume `H⁶` of the anisotropic fundamental cell. -/
theorem volume_bourgainParabolaFundamentalCell
    (H : ℕ) :
    volume (bourgainParabolaFundamentalCell H) =
      ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) := by
  unfold bourgainParabolaFundamentalCell bourgainFullBox
    bourgainParabolaFundamentalHalfWidth
  rw [Real.volume_pi_Ioc, Fin.prod_univ_four]
  norm_num
  rw [← ENNReal.ofReal_pow]
  congr 1
  ring

/-- Matrix of the combined osculating-coordinate and physical parabola
dilation map. -/
def bourgainScaledOsculatingPhaseMatrix
    (scale a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  bourgainParabolaPhaseScaleMatrix scale *
    bourgainSquareRootPhaseCoordinateMatrix a b

/-- Function represented by the combined matrix. -/
def bourgainScaledOsculatingPhaseCoordinates
    (scale a b : ℝ) (x : BourgainPhaseSpace) : BourgainPhaseSpace :=
  bourgainParabolaPhaseScale scale
    (bourgainSquareRootPhaseCoordinates a b x)

theorem bourgainScaledOsculatingPhaseMatrix_mulVec
    (scale a b : ℝ) (x : BourgainPhaseSpace) :
    (bourgainScaledOsculatingPhaseMatrix scale a b).mulVec x =
      bourgainScaledOsculatingPhaseCoordinates scale a b x := by
  unfold bourgainScaledOsculatingPhaseMatrix
    bourgainScaledOsculatingPhaseCoordinates
  rw [← Matrix.mulVec_mulVec,
    bourgainParabolaPhaseScaleMatrix_mulVec]
  rfl

/-- Exact determinant of the combined phase map. -/
theorem det_bourgainScaledOsculatingPhaseMatrix
    {scale a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (bourgainScaledOsculatingPhaseMatrix scale a b).det =
      scale ^ (6 : ℕ) *
        (3 * (b - a) ^ (4 : ℕ) /
          (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))) := by
  unfold bourgainScaledOsculatingPhaseMatrix
  rw [Matrix.det_mul, det_bourgainParabolaPhaseScaleMatrix,
    det_bourgainSquareRootPhaseCoordinateMatrix ha hb]

/-- Pullback of one fundamental period cell. -/
def bourgainOsculatingFundamentalCell
    (H : ℕ) (scale a b : ℝ) : Set BourgainPhaseSpace :=
  bourgainScaledOsculatingPhaseCoordinates scale a b ⁻¹'
    bourgainParabolaFundamentalCell H

/-- Exact Lebesgue pushforward under the combined phase map. -/
theorem map_bourgainScaledOsculatingPhaseMatrix_volume
    {scale a b : ℝ} (hscale : scale ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    Measure.map
        (Matrix.toLin'
          (bourgainScaledOsculatingPhaseMatrix scale a b))
        volume =
      ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| •
        volume := by
  have hb : 0 < b := ha.trans hab
  have hdet :
      (bourgainScaledOsculatingPhaseMatrix scale a b).det ≠ 0 := by
    rw [det_bourgainScaledOsculatingPhaseMatrix ha.ne' hb.ne']
    apply mul_ne_zero (pow_ne_zero 6 hscale)
    exact ne_of_gt
      (div_pos
        (mul_pos (by norm_num) (pow_pos (sub_pos.mpr hab) 4))
        (mul_pos (mul_pos (by norm_num) (pow_pos ha 3))
          (pow_pos hb 3)))
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
  rw [det_bourgainScaledOsculatingPhaseMatrix ha.ne' hb.ne']

/-- Exact volume of the pulled-back anisotropic fundamental cell. -/
theorem volume_bourgainOsculatingFundamentalCell
    (H : ℕ) {scale a b : ℝ} (hscale : scale ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    volume (bourgainOsculatingFundamentalCell H scale a b) =
      ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
        ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) := by
  let M := bourgainScaledOsculatingPhaseMatrix scale a b
  have hM : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hcell := measurableSet_bourgainParabolaFundamentalCell H
  have hcoord (x : BourgainPhaseSpace) :
      Matrix.toLin' M x =
        bourgainScaledOsculatingPhaseCoordinates scale a b x := by
    rw [Matrix.toLin'_apply]
    exact bourgainScaledOsculatingPhaseMatrix_mulVec scale a b x
  calc
    volume (bourgainOsculatingFundamentalCell H scale a b) =
        volume ((Matrix.toLin' M) ⁻¹'
          bourgainParabolaFundamentalCell H) := by
      congr 1
      ext x
      simp only [bourgainOsculatingFundamentalCell,
        Set.mem_preimage]
      rw [hcoord]
    _ = (Measure.map (Matrix.toLin' M) volume)
          (bourgainParabolaFundamentalCell H) := by
      exact (Measure.map_apply hM hcell).symm
    _ =
        (ENNReal.ofReal
            |(scale ^ (6 : ℕ) *
              (3 * (b - a) ^ (4 : ℕ) /
                (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| •
          volume) (bourgainParabolaFundamentalCell H) := by
      rw [show M =
          bourgainScaledOsculatingPhaseMatrix scale a b by rfl,
        map_bourgainScaledOsculatingPhaseMatrix_volume hscale ha hab]
    _ = _ := by
      rw [Measure.smul_apply,
        volume_bourgainParabolaFundamentalCell]
      rfl

end

end RHTower
