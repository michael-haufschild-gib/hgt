import GaloisForLFunctions.HTGeometry.GomesDerivativeParityGeneratedAlgebra

/-!
# All formal differentiation series are linear over the two-chain scalar center

An arbitrary infinite formal function of D is a scalar formal multiple of I plus
another scalar formal multiple of D. In particular actual translations and their
inverses already lie in every reflection-generated algebra.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- Every formal differentiation series is exactly linear in D over the scalar two-chain center. -/
theorem gomesFormalSeriesDerivativePowerMatrixHom_two_eq_linear (F : PowerSeries K) :
    gomesFormalSeriesDerivativePowerMatrixHom K 2 F =
      gomesFormalCoefficientResidue K 2 0 F • (1 : Matrix (Fin 2) (Fin 2) (PowerSeries K)) +
        gomesFormalCoefficientResidue K 2 1 F • gomesEvenOddDerivativeMatrix K := by
  rw [gomesFormalSeriesDerivativePowerMatrixHom_two]
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, gomesEvenOddDerivativeMatrix, smul_eq_mul, mul_comm]

/-- Every formal function of D belongs to every reflection-generated algebra over the scalar center. -/
theorem gomesFormalSeriesMatrix_mem_derivativeReflectionGeneratedAlgebra (c : K) (F : PowerSeries K) :
    gomesFormalSeriesDerivativePowerMatrixHom K 2 F ∈ gomesDerivativeReflectionGeneratedAlgebra K c := by
  rw [gomesFormalSeriesDerivativePowerMatrixHom_two_eq_linear]
  exact (gomesDerivativeReflectionGeneratedAlgebra K c).add_mem
    ((gomesDerivativeReflectionGeneratedAlgebra K c).smul_mem
      (gomesDerivativeReflectionGeneratedAlgebra K c).one_mem _)
    ((gomesDerivativeReflectionGeneratedAlgebra K c).smul_mem
      (gomesDerivativeReflectionGeneratedAlgebra_derivative_mem K c) _)

/-- Opposite exact formal-exponential translation matrices multiply to the identity. -/
theorem gomesFormalTranslationMatrix_mul_neg (c : K) :
    gomesFormalSeriesDerivativePowerMatrixHom K 2 (PowerSeries.rescale c (PowerSeries.exp K)) *
      gomesFormalSeriesDerivativePowerMatrixHom K 2 (PowerSeries.rescale (-c) (PowerSeries.exp K)) = 1 := by
  rw [← map_mul, PowerSeries.exp_mul_exp_eq_exp_add, add_neg_cancel,
    PowerSeries.rescale_zero_apply, PowerSeries.constantCoeff_exp, map_one, map_one]

/-- Multiplying reflection by the inverse translation recovers parity at every center. -/
theorem gomesPolynomialReflectionMatrix_mul_inverse_translation (c : K) :
    gomesPolynomialReflectionMatrix K c *
      gomesFormalSeriesDerivativePowerMatrixHom K 2 (PowerSeries.rescale (-c) (PowerSeries.exp K)) =
        gomesPolynomialReflectionMatrix K 0 := by
  rw [gomesPolynomialReflectionMatrix_eq_parity_exponential, mul_assoc,
    gomesFormalTranslationMatrix_mul_neg, mul_one]

end GaloisForLFunctions.HTGeometry
