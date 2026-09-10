import GaloisForLFunctions.HTGeometry.GomesPolynomialReflectionMatrix

/-!
# Exact matrix generators extracted from differentiation and parity

Half-scaled sums and differences extract the two chain projections, the upper
transfer, and the formal-variable-scaled lower transfer. The unscaled lower
transfer remains outside the generated constant-line algebra.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- The constant formal half, built in the coefficient field. -/
def gomesFormalHalf : PowerSeries K := PowerSeries.C (2 : K)⁻¹

/-- The formal half is a genuine additive half without assuming an extra formal-series instance. -/
theorem gomesFormalHalf_add_self : gomesFormalHalf K + gomesFormalHalf K = 1 := by
  have h : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ two_ne_zero]
  change PowerSeries.C (2 : K)⁻¹ + PowerSeries.C (2 : K)⁻¹ = 1
  rw [← map_add, h, map_one]

/-- Parity extracts the even-chain projection by an exact half-scaled sum. -/
theorem gomesParity_half_add_projection :
    gomesFormalHalf K • (1 + gomesPolynomialReflectionMatrix K 0) =
      ( !![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (PowerSeries K)) := by
  rw [gomesPolynomialReflectionMatrix_zero]
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, Matrix.smul_apply, smul_eq_mul, mul_add, gomesFormalHalf_add_self]

/-- Parity extracts the odd-chain projection by an exact half-scaled difference. -/
theorem gomesParity_half_sub_projection :
    gomesFormalHalf K • (1 - gomesPolynomialReflectionMatrix K 0) =
      ( !![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (PowerSeries K)) := by
  rw [gomesPolynomialReflectionMatrix_zero]
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, Matrix.smul_apply, smul_eq_mul, sub_eq_add_neg, mul_add,
    gomesFormalHalf_add_self]

/-- Differentiation and parity extract the unscaled odd-to-even transfer. -/
theorem gomesParity_half_add_derivative_upperTransfer :
    gomesFormalHalf K • (gomesEvenOddDerivativeMatrix K +
      gomesPolynomialReflectionMatrix K 0 * gomesEvenOddDerivativeMatrix K) =
        ( !![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (PowerSeries K)) := by
  rw [gomesPolynomialReflectionMatrix_zero]
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, Matrix.smul_apply, smul_eq_mul,
    gomesEvenOddDerivativeMatrix, mul_add, gomesFormalHalf_add_self]

/-- The opposite transfer is extracted with precisely one formal-variable factor. -/
theorem gomesParity_half_sub_derivative_lowerTransfer :
    gomesFormalHalf K • (gomesEvenOddDerivativeMatrix K -
      gomesPolynomialReflectionMatrix K 0 * gomesEvenOddDerivativeMatrix K) =
        ( !![0, 0; PowerSeries.X, 0] : Matrix (Fin 2) (Fin 2) (PowerSeries K)) := by
  rw [gomesPolynomialReflectionMatrix_zero]
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, Matrix.smul_apply, smul_eq_mul,
    gomesEvenOddDerivativeMatrix, sub_eq_add_neg, mul_add, ← add_mul,
    gomesFormalHalf_add_self]

omit [CharZero K] in
/-- Every boundary-compatible matrix is an exact linear combination of the four extracted generators. -/
theorem gomesFormalConstantLine_matrix_decomposition (a b c d : PowerSeries K) :
    ( !![a, b; PowerSeries.X * c, d] : Matrix (Fin 2) (Fin 2) (PowerSeries K)) =
      a • !![1, 0; 0, 0] + b • !![0, 1; 0, 0] +
        c • !![0, 0; PowerSeries.X, 0] + d • !![0, 0; 0, 1] := by
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, smul_eq_mul, mul_comm]

end GaloisForLFunctions.HTGeometry
