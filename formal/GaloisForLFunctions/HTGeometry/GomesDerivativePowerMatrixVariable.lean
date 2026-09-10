import GaloisForLFunctions.HTGeometry.GomesFormalSeriesDerivativePowerMatrix

/-!
# The central formal variable in derivative-power coordinates

The m-th power of the first derivative becomes the scalar formal variable in
its m-chain model. This identifies the center's variable without any finite
truncation or numerical evaluation.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- The formal m-th monomial acts as the actual m-th polynomial derivative. -/
theorem gomesFormalSeriesPolynomialOperator_X_pow (m : ℕ) :
    gomesFormalSeriesPolynomialOperator K (PowerSeries.X ^ m) =
      (Polynomial.derivative ^ m : Module.End K K[X]) := by
  change gomesFormalSeriesPolynomialAlgHom K (PowerSeries.X ^ m) = _
  rw [map_pow, gomesFormalSeriesPolynomialAlgHom_apply, gomesFormalSeriesPolynomialOperator_X]

/-- The formal m-th monomial becomes the scalar formal variable in the m-chain model. -/
theorem gomesFormalSeriesDerivativePowerMatrixHom_X_pow (m : ℕ) [NeZero m] :
    gomesFormalSeriesDerivativePowerMatrixHom K m (PowerSeries.X ^ m) =
      Matrix.scalar (Fin m) (PowerSeries.X : PowerSeries K) := by
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n (gomesPolynomialDerivativePowerCommutantEquiv K m
    (gomesFormalSeriesDerivativePowerHom K m (PowerSeries.X ^ m)) i j) = _
  rw [gomesPolynomialDerivativePowerCommutant_matrix_coeff]
  change (gomesPolynomialResidueChainEquiv K m
    (gomesFormalSeriesPolynomialOperator K (PowerSeries.X ^ m)
      (gomesDividedMonomialBasis K (n * m + j.val))) i).coeff 0 = _
  rw [gomesFormalSeriesPolynomialOperator_X_pow]
  cases n with
  | zero =>
      rw [Nat.zero_mul, Nat.zero_add, gomesDividedMonomialBasis_derivative_pow_residue_zero, map_zero]
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite, PowerSeries.coeff_X]
  | succ n =>
      rw [gomesDividedMonomialBasis_derivative_pow_residue_succ, gomesPolynomialResidueChainEquiv_basis]
      by_cases hij : i = j
      · subst j
        simp [Matrix.scalar_apply, gomesDividedMonomialBasis_coeff_zero,
          PowerSeries.coeff_X]
      · simp [Matrix.scalar_apply, hij]

/-- The matrix for first differentiation is an exact m-th root of the central formal variable. -/
theorem gomesFormalSeriesDerivativePowerMatrixHom_X_power (m : ℕ) [NeZero m] :
    gomesFormalSeriesDerivativePowerMatrixHom K m PowerSeries.X ^ m =
      Matrix.scalar (Fin m) (PowerSeries.X : PowerSeries K) := by
  rw [← map_pow, gomesFormalSeriesDerivativePowerMatrixHom_X_pow]

end GaloisForLFunctions.HTGeometry
