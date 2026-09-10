import GaloisForLFunctions.HTGeometry.GomesPolynomialReflectionSymmetry
import GaloisForLFunctions.HTGeometry.GomesEvenOddFormalMatrix

/-!
# Exact formal matrices of affine polynomial reflections

Every reflection is represented in the full second-derivative commutant. Parity
is diagonal; a general center multiplies it by the exact formal-exponential
translation matrix. Squaring the reflection gives a formal hyperbolic identity.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- The full formal matrix of literal polynomial reflection by c-X. -/
def gomesPolynomialReflectionMatrix (c : K) : Matrix (Fin 2) (Fin 2) (PowerSeries K) :=
  gomesPolynomialDerivativePowerCommutantEquiv K 2 (gomesPolynomialReflectionSymmetry K c)

/-- Parity is the diagonal sign matrix in the actual divided-monomial chain coordinates. -/
theorem gomesPolynomialReflectionMatrix_zero :
    gomesPolynomialReflectionMatrix K 0 = !![1, 0; 0, -1] := by
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n (gomesPolynomialDerivativePowerCommutantEquiv K 2
    (gomesPolynomialReflectionSymmetry K 0) i j) = _
  rw [gomesPolynomialDerivativePowerCommutant_matrix_coeff]
  change (gomesPolynomialResidueChainEquiv K 2
    (gomesPolynomialReflectionEnd K 0 (gomesDividedMonomialBasis K (n * 2 + j.val))) i).coeff 0 = _
  rw [gomesPolynomialReflectionEnd_zero_basis, map_smul, gomesPolynomialResidueChainEquiv_basis]
  change ((-1 : K) ^ (n * 2 + j.val) • ((Pi.single j (gomesDividedMonomialBasis K n) : Fin 2 → K[X]) i)).coeff 0 = _
  rw [Polynomial.coeff_smul]
  revert i j
  by_cases hn : n = 0 <;> simp [Fin.forall_fin_two, Pi.single_apply,
    gomesDividedMonomialBasis_coeff_zero, PowerSeries.coeff_one, hn]

/-- The exact reflection matrix is parity times the formal-exponential translation matrix. -/
theorem gomesPolynomialReflectionMatrix_eq_parity_exponential (c : K) :
    gomesPolynomialReflectionMatrix K c =
      gomesPolynomialReflectionMatrix K 0 *
        gomesFormalSeriesDerivativePowerMatrixHom K 2 (PowerSeries.rescale c (PowerSeries.exp K)) := by
  change gomesPolynomialDerivativePowerCommutantEquiv K 2 (gomesPolynomialReflectionSymmetry K c) =
    gomesPolynomialDerivativePowerCommutantEquiv K 2 (gomesPolynomialReflectionSymmetry K 0) *
      gomesPolynomialDerivativePowerCommutantEquiv K 2
        (gomesFormalSeriesDerivativePowerHom K 2 (PowerSeries.rescale c (PowerSeries.exp K)))
  rw [← map_mul]
  apply (gomesPolynomialDerivativePowerCommutantEquiv K 2).congr_arg
  apply Subtype.ext
  change gomesPolynomialReflectionEnd K c =
    gomesPolynomialReflectionEnd K 0 *
      gomesFormalSeriesPolynomialOperator K (PowerSeries.rescale c (PowerSeries.exp K))
  rw [gomesFormalExponentialOperator_eq_taylor, gomesPolynomialReflectionEnd_eq_parity_taylor]

/-- The compressed even formal exponential at an arbitrary reflection center. -/
def gomesFormalEvenExponential (c : K) : PowerSeries K :=
  gomesFormalCoefficientResidue K 2 0 (PowerSeries.rescale c (PowerSeries.exp K))

/-- The compressed odd formal exponential at an arbitrary reflection center. -/
def gomesFormalOddExponential (c : K) : PowerSeries K :=
  gomesFormalCoefficientResidue K 2 1 (PowerSeries.rescale c (PowerSeries.exp K))

/-- Closed exact matrix formula for every affine polynomial reflection. -/
theorem gomesPolynomialReflectionMatrix_eq (c : K) :
    gomesPolynomialReflectionMatrix K c =
      !![gomesFormalEvenExponential K c, gomesFormalOddExponential K c;
        -PowerSeries.X * gomesFormalOddExponential K c, -gomesFormalEvenExponential K c] := by
  rw [gomesPolynomialReflectionMatrix_eq_parity_exponential, gomesPolynomialReflectionMatrix_zero,
    gomesFormalSeriesDerivativePowerMatrixHom_two]
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    gomesFormalEvenExponential, gomesFormalOddExponential]

/-- Every formal reflection matrix is an involution. -/
theorem gomesPolynomialReflectionMatrix_sq (c : K) :
    gomesPolynomialReflectionMatrix K c ^ 2 = 1 := by
  change gomesPolynomialDerivativePowerCommutantEquiv K 2
    (gomesPolynomialReflectionSymmetry K c) ^ 2 = 1
  rw [← map_pow, ← map_one (gomesPolynomialDerivativePowerCommutantEquiv K 2)]
  apply (gomesPolynomialDerivativePowerCommutantEquiv K 2).congr_arg
  apply Subtype.ext
  exact gomesPolynomialReflectionEnd_sq K c

/-- Reflection involutivity forces the exact formal hyperbolic identity for all centers. -/
theorem gomesFormalEvenOddExponential_identity (c : K) :
    gomesFormalEvenExponential K c ^ 2 -
      PowerSeries.X * gomesFormalOddExponential K c ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (PowerSeries K) => M 0 0)
    (gomesPolynomialReflectionMatrix_sq K c)
  rw [gomesPolynomialReflectionMatrix_eq] at h
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h
  convert h using 1 <;> simp
  ring

end GaloisForLFunctions.HTGeometry
