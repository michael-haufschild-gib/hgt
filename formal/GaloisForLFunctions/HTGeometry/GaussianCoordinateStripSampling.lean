import GaloisForLFunctions.HTGeometry.GaussianWeightedVerticalError

/-!
# Coordinate-weighted sampling of the full Gaussian strip error

An exact coordinate identity bounds simultaneous displaced samples using the
original polynomial and its coordinate multiple. All coefficients remain coupled.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory
noncomputable section
namespace GaloisForLFunctions

/-- The complete vertical error before any coefficient or divisor sum is estimated. -/
def entirePolynomialGaussianVerticalError (P : Polynomial ℝ) (x δ : ℝ) : ℂ :=
  entirePolynomialGaussian P ((x : ℂ) + (δ : ℂ) * Complex.I) - polyGaussSchwartz P x

/-- Exact transport of the complete vertical error under coordinate multiplication. -/
theorem entirePolynomialGaussianVerticalError_coordinate (P : Polynomial ℝ) (x δ : ℝ) :
    (x : ℂ) * entirePolynomialGaussianVerticalError P x δ =
      entirePolynomialGaussianVerticalError (Polynomial.X * P) x δ -
        (δ : ℂ) * Complex.I *
          (entirePolynomialGaussianVerticalError P x δ + polyGaussSchwartz P x) := by
  simpa only [entirePolynomialGaussianVerticalError, sub_add_cancel] using
    entirePolynomialGaussian_coordinate_error P x δ

/-- Coordinate-square error has two complete polynomial-error endpoints. -/
theorem entirePolynomialGaussianVerticalError_coordinate_sq_le (P : Polynomial ℝ)
    (R : ℝ≥0) (x : ℝ) (δ : Set.Icc (-(R : ℝ)) R) :
    x ^ 2 * ‖entirePolynomialGaussianVerticalError P x δ‖ ^ 2 ≤
      2 * ‖entirePolynomialGaussianVerticalError (Polynomial.X * P) x δ‖ ^ 2 +
      4 * (R : ℝ) ^ 2 * (‖entirePolynomialGaussianVerticalError P x δ‖ ^ 2 +
        ‖polyGaussSchwartz P x‖ ^ 2) := by
  have hsub (z w : ℂ) : ‖z - w‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le z w) 2
    nlinarith only [h, sq_nonneg (‖z‖ - ‖w‖)]
  have hadd (z w : ℂ) : ‖z + w‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
    simpa only [sub_neg_eq_add, norm_neg] using hsub z (-w)
  have hc := hsub (entirePolynomialGaussianVerticalError (Polynomial.X * P) x δ)
    (((δ : ℝ) : ℂ) * Complex.I *
      (entirePolynomialGaussianVerticalError P x δ + polyGaussSchwartz P x))
  rw [← entirePolynomialGaussianVerticalError_coordinate, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, mul_pow, sq_abs] at hc
  have hδ : (δ : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (δ : ℝ))
      (abs_le.mpr δ.property) 2
  have ha := mul_le_mul hδ
    (hadd (entirePolynomialGaussianVerticalError P x δ) (polyGaussSchwartz P x))
    (sq_nonneg _) (sq_nonneg (R : ℝ))
  nlinarith only [hc, ha]

/-- Squared grid ceiling for the full error, in a convenient exact-error notation. -/
theorem gaussianVerticalError_grid_le (P : Polynomial ℝ) (R : ℝ≥0)
    (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ)
    (δ : ℕ → Set.Icc (-(R : ℝ)) R) :
    (h : ℝ) * ∑ j ∈ Finset.range N,
      ‖entirePolynomialGaussianVerticalError P (a + ((j : ℝ) + (s j : ℝ)) * h) (δ j)‖ ^ 2 ≤
      gaussianStripSamplingFactor P.natDegree h ^ 2 *
        verticalPolynomialGaussianDefect P.natDegree R ^ 2 *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  rw [gaussianStripSamplingFactor, Real.sq_sqrt (by positivity)]
  exact gaussianPolynomial_grid_variableShift_error P R a h s N δ

/-- A common successor-degree ceiling controls both weighted-error endpoints. -/
def gaussianCoordinateStripBudget (d : ℕ) (R : ℝ≥0) : ℝ :=
  2 * (Real.sqrt (4 * π * ((d : ℝ) + 1)) / (2 * π)) ^ 2 *
      verticalPolynomialGaussianDefect (d + 1) R ^ 2 +
    4 * (R : ℝ) ^ 2 * (verticalPolynomialGaussianDefect (d + 1) R ^ 2 + 1)

/-- All coordinate-weighted grid errors are controlled in the original Gaussian norm. -/
theorem gaussianVerticalError_grid_coordinate_le (P : Polynomial ℝ) (R : ℝ≥0)
    (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ)
    (δ : ℕ → Set.Icc (-(R : ℝ)) R) :
    (h : ℝ) * ∑ j ∈ Finset.range N,
      (a + ((j : ℝ) + (s j : ℝ)) * h) ^ 2 *
        ‖entirePolynomialGaussianVerticalError P
          (a + ((j : ℝ) + (s j : ℝ)) * h) (δ j)‖ ^ 2 ≤
      gaussianStripSamplingFactor (P.natDegree + 1) h ^ 2 *
        gaussianCoordinateStripBudget P.natDegree R *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  let M := ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖
  let C := gaussianStripSamplingFactor (P.natDegree + 1) h ^ 2
  let E := verticalPolynomialGaussianDefect (P.natDegree + 1) R ^ 2
  let A := Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) / (2 * π)
  let x (j : ℕ) := a + ((j : ℝ) + (s j : ℝ)) * h
  let e (Q : Polynomial ℝ) (j : ℕ) := ‖entirePolynomialGaussianVerticalError Q (x j) (δ j)‖ ^ 2
  have hCE (Q : Polynomial ℝ) (hd : Q.natDegree ≤ P.natDegree + 1) :
      (h : ℝ) * ∑ j ∈ Finset.range N, e Q j ≤
        C * E * ‖(polyGaussSchwartz Q).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    have hc := pow_le_pow_left₀ (gaussianStripSamplingFactor_nonneg _ _)
      (gaussianStripSamplingFactor_mono h hd) 2
    have he := pow_le_pow_left₀ (verticalPolynomialGaussianDefect_nonneg _ _)
      (verticalPolynomialGaussianDefect_mono R hd) 2
    exact (gaussianVerticalError_grid_le Q R a h s N δ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hc he (sq_nonneg _) (sq_nonneg _))
        (sq_nonneg _))
  have hd : (Polynomial.X * P).natDegree ≤ P.natDegree + 1 := by
    simpa only [Polynomial.natDegree_X, add_comm] using
      Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℝ)) (q := P)
  have hXnorm : ‖(polyGaussSchwartz (Polynomial.X * P)).toLp 2 (volume : Measure ℝ)‖ ≤ A * M := by
    rw [← mulXCLM_polyGauss_eq, div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mpr
    simpa only [M, mul_comm] using gaussianPolynomialCoordinateNorm_le P
  have hX := (hCE (Polynomial.X * P) hd).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hXnorm 2)
      (by dsimp [C, E]; positivity))
  have hP := hCE P (Nat.le_succ _)
  have hf := pow_le_pow_left₀ (norm_nonneg _)
    (norm_gaussianGridSamples_polyGauss_le_stripFactor P a h s N) 2
  rw [gaussianGridSamples_norm_sq, mul_pow] at hf
  have hc := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (gaussianStripSamplingFactor_nonneg P.natDegree h)
      (gaussianStripSamplingFactor_mono h (Nat.le_succ P.natDegree)) 2) (sq_nonneg M)
  have hf' := hf.trans hc
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum
    (fun j (_ : j ∈ Finset.range N) => entirePolynomialGaussianVerticalError_coordinate_sq_le
      P R (x j) (δ j))) h.coe_nonneg
  simp only [Finset.sum_add_distrib, Finset.mul_sum] at hs
  change (h : ℝ) * ∑ j ∈ Finset.range N, x j ^ 2 * e P j ≤ _
  unfold gaussianCoordinateStripBudget
  change _ ≤ C * (2 * A ^ 2 * E + 4 * (R : ℝ) ^ 2 * (E + 1)) * M ^ 2
  have hPX := add_le_add (mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 4 * (R : ℝ) ^ 2))
    (mul_le_mul_of_nonneg_left hf' (by positivity : 0 ≤ 4 * (R : ℝ) ^ 2))
  dsimp only [e, x, M] at hX hP hPX hs ⊢
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  nlinarith only [hX, hPX, hs]

end GaloisForLFunctions
