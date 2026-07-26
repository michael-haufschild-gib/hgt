/-
# Natural-scale anisotropic cell transfer

The dilation `(x₁,x₂,x₃,x₄) ↦ (Hx₁,H²x₂,Hx₃,H²x₄)` has determinant
`H⁶`.  This module transfers any nonnegative measurable integrand from
Bourgain's centered period cell to the normalized four-cube with exactly
that factor.
-/
import GaloisForLFunctions.RHTower.BourgainExactOsculatingCubeDecoupling
import GaloisForLFunctions.RHTower.BourgainAnisotropicFundamentalCell

open MeasureTheory

namespace RHTower

noncomputable section

/-- Natural coordinate scaling agrees with the parabola phase dilation. -/
theorem bourgainCoordinateScale_natural_eq_phaseScale
    (H : ℕ) (x : BourgainPhaseSpace) :
    bourgainCoordinateScale
        (bourgainIndependentParabolaNaturalScale H) x =
      bourgainParabolaPhaseScale (H : ℝ) x := by
  ext j
  fin_cases j <;>
    simp [bourgainCoordinateScale,
      bourgainIndependentParabolaNaturalScale,
      bourgainParabolaPhaseScale, Matrix.cons_val]

/-- The inverse image of the centered natural period cell lies in the
normalized four-cube. -/
theorem preimage_parabolaFundamentalCell_naturalScale_subset_fourCube
    {H : ℕ} (hH : 0 < H) :
    bourgainParabolaPhaseScale (H : ℝ) ⁻¹'
        bourgainParabolaFundamentalCell H ⊆
      bourgainFourCube := by
  intro x hx
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  change ‖x‖ ≤ 1
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  rw [Real.norm_eq_abs, abs_le]
  unfold bourgainParabolaFundamentalCell bourgainFullBox
    bourgainParabolaFundamentalHalfWidth at hx
  have hj := hx j
  fin_cases j <;>
    simp [bourgainParabolaPhaseScale, Matrix.cons_val] at hj ⊢
  all_goals constructor <;> nlinarith [sq_pos_of_pos hHr]

/-- Exact `H⁶` enlargement from the centered anisotropic period cell to the
normalized four-cube. -/
theorem setLIntegral_bourgainParabolaFundamentalCell_le_naturalScale_fourCube
    (H : ℕ) (hH : 0 < H)
    (g : BourgainPhaseSpace → ENNReal) (hg : Measurable g) :
    (∫⁻ y in bourgainParabolaFundamentalCell H, g y) ≤
      ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
        ∫⁻ x in bourgainFourCube,
          g (bourgainCoordinateScale
            (bourgainIndependentParabolaNaturalScale H) x) := by
  let M := bourgainParabolaPhaseScaleMatrix (H : ℝ)
  let S : ENNReal := ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ))
  let R : ENNReal :=
    ENNReal.ofReal |(((H : ℝ) ^ (6 : ℕ))⁻¹)|
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hscale : (H : ℝ) ≠ 0 := hHr.ne'
  have hM : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hcell := measurableSet_bourgainParabolaFundamentalCell H
  have hcoord (x : BourgainPhaseSpace) :
      Matrix.toLin' M x =
        bourgainParabolaPhaseScale (H : ℝ) x := by
    rw [Matrix.toLin'_apply]
    exact bourgainParabolaPhaseScaleMatrix_mulVec (H : ℝ) x
  have hset :
      (bourgainParabolaPhaseScale (H : ℝ)) ⁻¹'
          bourgainParabolaFundamentalCell H =
        (Matrix.toLin' M) ⁻¹'
          bourgainParabolaFundamentalCell H := by
    ext x
    simp only [Set.mem_preimage]
    rw [hcoord]
  have hfun :
      (fun x : BourgainPhaseSpace =>
        g (bourgainParabolaPhaseScale (H : ℝ) x)) =
        fun x => g (Matrix.toLin' M x) := by
    funext x
    rw [hcoord]
  have hpre :
      (∫⁻ x in
          (bourgainParabolaPhaseScale (H : ℝ)) ⁻¹'
            bourgainParabolaFundamentalCell H,
          g (bourgainParabolaPhaseScale (H : ℝ) x)) =
        R * ∫⁻ y in bourgainParabolaFundamentalCell H, g y := by
    calc
      (∫⁻ x in
          (bourgainParabolaPhaseScale (H : ℝ)) ⁻¹'
            bourgainParabolaFundamentalCell H,
          g (bourgainParabolaPhaseScale (H : ℝ) x)) =
        ∫⁻ x in (Matrix.toLin' M) ⁻¹'
            bourgainParabolaFundamentalCell H,
          g (Matrix.toLin' M x) := by
            rw [hset, hfun]
      _ = ∫⁻ y in bourgainParabolaFundamentalCell H, g y ∂
          Measure.map (Matrix.toLin' M) volume := by
            symm
            exact setLIntegral_map hcell hg hM
      _ = ∫⁻ y in bourgainParabolaFundamentalCell H, g y ∂
          (R • volume) := by
            dsimp [M, R]
            rw [map_bourgainParabolaPhaseScaleMatrix_volume hscale]
      _ = R * ∫⁻ y in bourgainParabolaFundamentalCell H, g y := by
            rw [setLIntegral_smul_measure]
            rfl
  have hsubset :=
    preimage_parabolaFundamentalCell_naturalScale_subset_fourCube hH
  have hmono :
      (∫⁻ x in
          (bourgainParabolaPhaseScale (H : ℝ)) ⁻¹'
            bourgainParabolaFundamentalCell H,
          g (bourgainParabolaPhaseScale (H : ℝ) x)) ≤
        ∫⁻ x in bourgainFourCube,
          g (bourgainParabolaPhaseScale (H : ℝ) x) :=
    lintegral_mono_set hsubset
  have hSR : S * R = 1 := by
    dsimp [S, R]
    rw [abs_of_pos (inv_pos.mpr (pow_pos hHr 6))]
    rw [← ENNReal.ofReal_mul (pow_nonneg hHr.le 6)]
    rw [mul_inv_cancel₀ (ne_of_gt (pow_pos hHr 6))]
    simp
  calc
    (∫⁻ y in bourgainParabolaFundamentalCell H, g y) =
        S * (R * ∫⁻ y in bourgainParabolaFundamentalCell H, g y) := by
          rw [← mul_assoc, hSR, one_mul]
    _ = S * (∫⁻ x in
        (bourgainParabolaPhaseScale (H : ℝ)) ⁻¹'
          bourgainParabolaFundamentalCell H,
        g (bourgainParabolaPhaseScale (H : ℝ) x)) := by
          rw [hpre]
    _ ≤ S * ∫⁻ x in bourgainFourCube,
        g (bourgainParabolaPhaseScale (H : ℝ) x) :=
      mul_le_mul_right hmono S
    _ = ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
        ∫⁻ x in bourgainFourCube,
          g (bourgainCoordinateScale
            (bourgainIndependentParabolaNaturalScale H) x) := by
      dsimp [S]
      congr 1
      apply lintegral_congr
      intro x
      rw [bourgainCoordinateScale_natural_eq_phaseScale]

end

end RHTower
