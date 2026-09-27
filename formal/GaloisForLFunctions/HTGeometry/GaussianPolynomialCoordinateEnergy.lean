import GaloisForLFunctions.HTGeometry.ComplexGaussianPolynomialTranslation

/-!
# Coordinate and full derivative bounds for polynomial Gaussians

The finite Hermite spectral ceiling controls both oscillator operators. Their
sum and difference bound multiplication by the coordinate and differentiation
of the entire polynomial Gaussian, uniformly over its coefficients.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions

/-- Creation costs at most the square root of the next Hermite eigenvalue. -/
theorem gaussianPolynomialCreationNorm_le (P : Polynomial ℝ) :
    ‖(creationCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ≤
      Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  have hshift :
      ‖(numberCLM (polyGaussSchwartz P) +
          (4 * (π : ℂ)) • polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
        (4 * π * ((P.natDegree : ℝ) + 1)) *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
    rw [toLp_add]
    calc
      _ ≤ ‖(numberCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ +
          ‖((4 * (π : ℂ)) • polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ :=
        norm_add_le _ _
      _ ≤ 4 * π * P.natDegree *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ +
          4 * π * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
        rw [norm_toLp_smul_four_pi]
        exact add_le_add (numberCLM_polyGauss_norm_le P) le_rfl
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 4 * π * ((P.natDegree : ℝ) + 1))]
  calc
    _ ≤ ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ *
        ‖(numberCLM (polyGaussSchwartz P) +
          (4 * (π : ℂ)) • polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ :=
      norm_toLp_creationCLM_sq_le _
    _ ≤ ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ *
        ((4 * π * ((P.natDegree : ℝ) + 1)) *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖) :=
      mul_le_mul_of_nonneg_left hshift (norm_nonneg _)
    _ = _ := by ring

/-- A common spectral ceiling for annihilation and creation. -/
theorem gaussianPolynomialAnnihilationNorm_le (P : Polynomial ℝ) :
    ‖(annihilationCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ≤
      Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  rw [annihilationCLM_polyGaussSchwartz]
  refine (gaussianPolynomialDerivativeNorm_le P).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.sqrt_le_sqrt
  nlinarith only [Real.pi_pos]

/-- Coordinate multiplication has a square-root degree bound in Gaussian energy. -/
theorem gaussianPolynomialCoordinateNorm_le (P : Polynomial ℝ) :
    2 * π * ‖(mulXCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ≤
      Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  have hA := gaussianPolynomialCreationNorm_le P
  have hB := gaussianPolynomialAnnihilationNorm_le P
  have htriangle := norm_add_le
    ((creationCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ))
    ((annihilationCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ))
  rw [← toLp_add, creation_add_annihilation, norm_toLp_smul_four_pi] at htriangle
  nlinarith only [hA, hB, htriangle]

/-- The derivative of the entire polynomial Gaussian obeys the same ceiling. -/
theorem gaussianPolynomialFullDerivativeNorm_le (P : Polynomial ℝ) :
    ‖(derivSCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ≤
      Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  have hA := gaussianPolynomialCreationNorm_le P
  have hB := gaussianPolynomialAnnihilationNorm_le P
  have htriangle := norm_sub_le
    ((annihilationCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ))
    ((creationCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ))
  rw [← toLp_sub, annihilation_sub_creation, toLp_smul, norm_smul,
    norm_ofNat] at htriangle
  linarith only [hA, hB, htriangle]

end GaloisForLFunctions
