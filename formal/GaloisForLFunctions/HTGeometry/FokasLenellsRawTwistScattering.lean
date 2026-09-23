import GaloisForLFunctions.HTGeometry.FokasLenellsRawTwistEndpoints

/-!
# Imaginary-ray covariance of the actual scattering coefficients

Every term in the genuine endpoint product has its total-degree phase.
The resulting fifth-coefficient covariance, together with the actual
reverse-reflection identity, identifies the fifth traces of the two
squared-spectral rays.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem swap_conjugation_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (swapMatrix*A*swapMatrix)*(swapMatrix*B*swapMatrix) = swapMatrix*(A*B)*swapMatrix := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc swapMatrix swapMatrix, swapMatrix_squared, one_mul]

private theorem swap_conjugation_adjugate (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (swapMatrix*A*swapMatrix).adjugate = swapMatrix*A.adjugate*swapMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [swapMatrix]

private theorem adjugate_complex_smul (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (c • A).adjugate = c • A.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, smul_eq_mul]

private theorem adjugate_matrix_neg (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (-A).adjugate = -A.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]

private theorem swap_conjugation_upper_diag (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (swapMatrix*A*swapMatrix) 1 1 = A 0 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [swapMatrix]

private theorem swap_conjugation_lower (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (swapMatrix*A*swapMatrix) 1 0 = A 0 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [swapMatrix]

theorem rawScatteringQuadraticCoefficient_twisted (q : SchwartzMap ℝ ℂ) :
    rawScatteringQuadraticCoefficient (twistedPotential q) =
      -(swapMatrix * rawScatteringQuadraticCoefficient q * swapMatrix) := by
  simp only [rawScatteringQuadraticCoefficient, rawQuadraticEndpointMatrix_twisted,
    rawFirstCoefficientMatrix_twisted]
  simp only [adjugate_matrix_neg, swap_conjugation_adjugate,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, I_mul_I, neg_one_smul, swap_conjugation_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul]
  module

theorem rawScatteringCubicCoefficient_twisted (q : SchwartzMap ℝ ℂ) :
    rawScatteringCubicCoefficient (twistedPotential q) =
      -I • (swapMatrix * rawScatteringCubicCoefficient q * swapMatrix) := by
  simp only [rawScatteringCubicCoefficient, rawCubicEndpointMatrix_twisted_zero,
    rawQuadraticEndpointMatrix_twisted, rawFirstCoefficientMatrix_twisted]
  simp only [adjugate_complex_smul, adjugate_matrix_neg, swap_conjugation_adjugate,
    Matrix.smul_mul, Matrix.mul_smul, neg_mul, mul_neg, swap_conjugation_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub]
  module

theorem rawScatteringFourthCoefficient_twisted (q : SchwartzMap ℝ ℂ) :
    rawScatteringFourthCoefficient (twistedPotential q) =
      swapMatrix * rawScatteringFourthCoefficient q * swapMatrix := by
  simp only [rawScatteringFourthCoefficient, rawQuarticEndpointMatrix_twisted,
    rawCubicEndpointMatrix_twisted_zero, rawQuadraticEndpointMatrix_twisted,
    rawFirstCoefficientMatrix_twisted]
  simp only [adjugate_complex_smul, adjugate_matrix_neg, swap_conjugation_adjugate,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul, mul_neg, neg_neg,
    I_mul_I, one_smul, swap_conjugation_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul]

/-- The conjectured fifth-coefficient twist law holds for the complete actual scattering coefficient. -/
theorem rawScatteringFifthCoefficient_twisted (q : SchwartzMap ℝ ℂ) :
    rawScatteringFifthCoefficient (twistedPotential q) =
      I • (swapMatrix * rawScatteringFifthCoefficient q * swapMatrix) := by
  simp only [rawScatteringFifthCoefficient, rawScatteringFifthRemainder, Complex.ofReal_zero,
    zero_pow (by omega : 2 ≠ 0), zero_pow (by omega : 3 ≠ 0), zero_pow (by omega : 4 ≠ 0),
    zero_pow (by omega : 5 ≠ 0), zero_smul, add_zero, rawQuinticEndpointMatrix_twisted_zero,
    rawQuarticEndpointMatrix_twisted, rawCubicEndpointMatrix_twisted_zero,
    rawQuadraticEndpointMatrix_twisted, rawFirstCoefficientMatrix_twisted]
  simp only [adjugate_complex_smul, adjugate_matrix_neg, swap_conjugation_adjugate,
    Matrix.smul_mul, Matrix.mul_smul, neg_mul, mul_neg, swap_conjugation_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub]
  module

/-- The second coefficient shows that the mixed derivative moment is invariant under the imaginary-ray twist. -/
theorem rawMixedTotal_twistedPotential (q : SchwartzMap ℝ ℂ) :
    rawMixedTotal (twistedPotential q) = rawMixedTotal q := by
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1)
    (rawScatteringQuadraticCoefficient_twisted q)
  change rawScatteringQuadraticCoefficient (twistedPotential q) 1 1 =
    -(swapMatrix * rawScatteringQuadraticCoefficient q * swapMatrix) 1 1 at he
  rw [swap_conjugation_upper_diag, rawScatteringQuadraticCoefficient_eq,
    rawScatteringQuadraticCoefficient_eq] at he
  simpa using he

/-- The actual reverse-reflection identity forces opposite fifth coefficients without a compatibility assumption. -/
theorem rawScatteringFifthCoefficient_upper_eq_neg_lower (q : SchwartzMap ℝ ℂ) :
    rawScatteringFifthCoefficient q 0 1 = -rawScatteringFifthCoefficient q 1 0 := by
  have he : Tendsto Real.exp atBot (𝓝[≠] (0 : ℝ)) :=
    Real.tendsto_exp_atBot_nhdsGT.mono_right (nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx))
  have hL := ((rawReflection_sub_cubic_quotient_tendsto q).comp he).neg
  have hU := (rawReverseReflection_sub_cubic_quotient_tendsto q).comp he
  change Tendsto (fun κ : ℝ => -((rawScatteringMatrix q (Real.exp κ) 1 0 -
    (Real.exp κ : ℂ)^(3 : ℕ)*(2*compatibilityMoment q))/(Real.exp κ : ℂ)^(5 : ℕ))) atBot
      (𝓝 (-rawScatteringFifthCoefficient q 1 0)) at hL
  change Tendsto (fun κ : ℝ => (rawScatteringMatrix q (Real.exp κ) 0 1 -
    (Real.exp κ : ℂ)^(3 : ℕ)*(-2*compatibilityMoment q))/(Real.exp κ : ℂ)^(5 : ℕ)) atBot
      (𝓝 (rawScatteringFifthCoefficient q 0 1)) at hU
  apply tendsto_nhds_unique hU
  apply hL.congr'
  apply Eventually.of_forall
  intro κ
  simp only [rawScatteringMatrix_exp_eq]
  change -((reflectionAmplitude q κ - (Real.exp κ : ℂ)^(3 : ℕ)*(2*compatibilityMoment q))/(Real.exp κ : ℂ)^(5 : ℕ)) =
    (reverseReflectionAmplitude q κ - (Real.exp κ : ℂ)^(3 : ℕ)*(-2*compatibilityMoment q))/(Real.exp κ : ℂ)^(5 : ℕ)
  rw [reverseReflectionAmplitude_eq_neg]
  ring

/-- The physical fifth reflection trace is the same on the real and imaginary rays. -/
theorem rawScatteringFifthCoefficient_twisted_lower (q : SchwartzMap ℝ ℂ) :
    rawScatteringFifthCoefficient (twistedPotential q) 1 0 = -I*rawScatteringFifthCoefficient q 1 0 := by
  rw [rawScatteringFifthCoefficient_twisted]
  change I*(swapMatrix * rawScatteringFifthCoefficient q * swapMatrix) 1 0 = _
  rw [swap_conjugation_lower, rawScatteringFifthCoefficient_upper_eq_neg_lower]
  ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
