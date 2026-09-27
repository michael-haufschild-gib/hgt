import GaloisForLFunctions.HTGeometry.GaussianCoordinateStripSampling

/-!
# Absorbing logarithmic sample density into Gaussian strip energy

The logarithmic cell-count weight is bounded by a freely scaled coordinate
square. Both resulting whole-polynomial grid energies have independent bounds.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory
noncomputable section
namespace GaloisForLFunctions

def gaussianLogSamplingWeight (r B : ℝ) : ℝ := 2 + Real.log (3 + B / r)

theorem gaussianLogSamplingWeight_pos (r B : {x : ℝ // 0 < x}) :
    0 < gaussianLogSamplingWeight r B := by
  have hr := r.property
  have hB := B.property
  have hl : 0 ≤ Real.log (3 + (B : ℝ) / (r : ℝ)) :=
    Real.log_nonneg (by have hp := div_pos hB hr; linarith only [hp])
  unfold gaussianLogSamplingWeight
  linarith only [hl]

/-- The logarithmic count in a cell is absorbed by a coordinate-square weight at any point in it. -/
theorem log_cell_le_gaussianLogSamplingWeight (j : ℕ) (s : Set.Icc (0 : ℝ) 1)
    (r B : {x : ℝ // 0 < x}) :
    1 + Real.log (3 + (j : ℝ)) ≤
      gaussianLogSamplingWeight r B *
        (1 + (((r : ℝ) * ((j : ℝ) + (s : ℝ))) / (B : ℝ)) ^ 2) := by
  let z := ((r : ℝ) * ((j : ℝ) + (s : ℝ))) / (B : ℝ)
  let L := 3 + (B : ℝ) / (r : ℝ)
  have hr := r.property
  have hB := B.property
  have hz : 0 ≤ z := div_nonneg (mul_nonneg hr.le (add_nonneg (Nat.cast_nonneg _) s.property.1)) hB.le
  have hL : 1 ≤ L := by dsimp [L]; have hh := div_pos hB hr; linarith only [hh]
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hid : ((B : ℝ) / (r : ℝ)) * z = (j : ℝ) + (s : ℝ) := by
    dsimp [z]
    field_simp
  have harg : 3 + (j : ℝ) ≤ L * (1 + z) := by
    dsimp only [L]
    nlinarith only [hid, hz, s.property.1, div_pos hB hr]
  have hl := Real.log_le_log (by positivity : 0 < 3 + (j : ℝ)) harg
  rw [Real.log_mul hLpos.ne' (by positivity : 1 + z ≠ 0)] at hl
  have hsmall := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + z)
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hzsq : z ≤ 1 + z ^ 2 := by nlinarith only [sq_nonneg (z - 1)]
  have hweight : z ^ 2 ≤ (2 + Real.log L) * z ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg z) (by linarith only [hlog])
  change 1 + Real.log (3 + (j : ℝ)) ≤ (2 + Real.log L) * (1 + z ^ 2)
  nlinarith only [hl, hsmall, hzsq, hweight]

/-- Budget for both full grid errors, before any count of actual Xi zeros is introduced. -/
def gaussianWeightedStripBudget (d : ℕ) (R : ℝ≥0) (B : ℝ) : ℝ :=
  verticalPolynomialGaussianDefect (d + 1) R ^ 2 + gaussianCoordinateStripBudget d R / B ^ 2

/-- The coordinate-weighted full strip error has a coefficient-uniform grid bound. -/
theorem gaussianVerticalError_grid_weighted_le (P : Polynomial ℝ) (R : ℝ≥0)
    (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ)
    (δ : ℕ → Set.Icc (-(R : ℝ)) R) (B : {B : ℝ // 0 < B}) :
    (h : ℝ) * ∑ j ∈ Finset.range N,
      (1 + ((a + ((j : ℝ) + (s j : ℝ)) * h) / (B : ℝ)) ^ 2) *
        ‖entirePolynomialGaussianVerticalError P
          (a + ((j : ℝ) + (s j : ℝ)) * h) (δ j)‖ ^ 2 ≤
      gaussianStripSamplingFactor (P.natDegree + 1) h ^ 2 *
        gaussianWeightedStripBudget P.natDegree R B *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have hC := pow_le_pow_left₀ (gaussianStripSamplingFactor_nonneg P.natDegree h)
    (gaussianStripSamplingFactor_mono h (Nat.le_succ _)) 2
  have hE := pow_le_pow_left₀ (verticalPolynomialGaussianDefect_nonneg P.natDegree R)
    (verticalPolynomialGaussianDefect_mono R (Nat.le_succ _)) 2
  have he := (gaussianVerticalError_grid_le P R a h s N δ).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul hC hE (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
  have hc := div_le_div_of_nonneg_right
    (gaussianVerticalError_grid_coordinate_le P R a h s N δ) (sq_nonneg (B : ℝ))
  have hid : (h : ℝ) * ∑ j ∈ Finset.range N,
      (1 + ((a + ((j : ℝ) + (s j : ℝ)) * h) / (B : ℝ)) ^ 2) *
        ‖entirePolynomialGaussianVerticalError P
          (a + ((j : ℝ) + (s j : ℝ)) * h) (δ j)‖ ^ 2 =
      (h : ℝ) * ∑ j ∈ Finset.range N,
        ‖entirePolynomialGaussianVerticalError P
          (a + ((j : ℝ) + (s j : ℝ)) * h) (δ j)‖ ^ 2 +
      ((h : ℝ) * ∑ j ∈ Finset.range N,
        (a + ((j : ℝ) + (s j : ℝ)) * h) ^ 2 *
          ‖entirePolynomialGaussianVerticalError P
            (a + ((j : ℝ) + (s j : ℝ)) * h) (δ j)‖ ^ 2) / (B : ℝ) ^ 2 := by
    simp only [add_mul, one_mul, div_pow, Finset.sum_add_distrib, mul_add]
    congr 1
    rw [mul_div_assoc, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid]
  refine (add_le_add he hc).trans_eq ?_
  unfold gaussianWeightedStripBudget
  ring

end GaloisForLFunctions
