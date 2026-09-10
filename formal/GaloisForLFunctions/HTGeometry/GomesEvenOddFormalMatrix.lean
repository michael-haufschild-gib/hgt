import GaloisForLFunctions.HTGeometry.GomesDerivativePowerMatrixVariable

/-!
# Exact even-odd matrices for all formal functions of differentiation

The first derivative becomes the companion matrix [[0,1],[X,0]]. Its matrix
centralizer forces the remaining entries of every formal differentiation series
from its first row, giving a complete and faithful two-chain representation.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- The first derivative in its even and odd divided-monomial chains. -/
def gomesEvenOddDerivativeMatrix : Matrix (Fin 2) (Fin 2) (PowerSeries K) :=
  !![0, 1; PowerSeries.X, 0]

/-- The first derivative has the exact formal companion matrix, with no truncation. -/
theorem gomesFormalSeriesDerivativePowerMatrixHom_two_X :
    gomesFormalSeriesDerivativePowerMatrixHom K 2 PowerSeries.X = gomesEvenOddDerivativeMatrix K := by
  let M := gomesFormalSeriesDerivativePowerMatrixHom K 2 (PowerSeries.X : PowerSeries K)
  have h00 : M 0 0 = 0 := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n
      (gomesFormalSeriesDerivativePowerMatrixHom K 2 PowerSeries.X 0 0) = _
    rw [gomesFormalSeriesDerivativePowerMatrixHom_first_row]
    have hindex : n * 2 ≠ 1 := by
      cases n with
      | zero => exact Nat.zero_ne_one
      | succ n =>
          rw [Nat.succ_mul]
          exact fun h => Nat.succ_ne_zero (n * 2) (Nat.succ.inj h)
    simp [PowerSeries.coeff_X, hindex]
  have h01 : M 0 1 = 1 := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n
      (gomesFormalSeriesDerivativePowerMatrixHom K 2 PowerSeries.X 0 1) = _
    rw [gomesFormalSeriesDerivativePowerMatrixHom_first_row]
    simp [PowerSeries.coeff_X, PowerSeries.coeff_one]
  have hs : M ^ 2 = Matrix.scalar (Fin 2) (PowerSeries.X : PowerSeries K) :=
    gomesFormalSeriesDerivativePowerMatrixHom_X_power K 2
  have h10 : M 1 0 = PowerSeries.X := by
    have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) (PowerSeries K) => N 0 0) hs
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, h00, h01] using h
  have h11 : M 1 1 = 0 := by
    have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) (PowerSeries K) => N 0 1) hs
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, h00, h01] using h
  change M = gomesEvenOddDerivativeMatrix K
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, gomesEvenOddDerivativeMatrix, h00, h01, h10, h11]

omit [CharZero K] in
/-- The complete centralizer equations of the two-chain derivative matrix. -/
theorem gomesEvenOddDerivativeMatrix_commutes_iff
    (M : Matrix (Fin 2) (Fin 2) (PowerSeries K)) :
    Commute M (gomesEvenOddDerivativeMatrix K) ↔
      M 1 0 = PowerSeries.X * M 0 1 ∧ M 1 1 = M 0 0 := by
  change M * gomesEvenOddDerivativeMatrix K = gomesEvenOddDerivativeMatrix K * M ↔ _
  constructor
  · intro h
    have h00 := congrArg (fun N : Matrix (Fin 2) (Fin 2) (PowerSeries K) => N 0 0) h
    have h01 := congrArg (fun N : Matrix (Fin 2) (Fin 2) (PowerSeries K) => N 0 1) h
    constructor
    · simpa [gomesEvenOddDerivativeMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using h00.symm
    · simpa [gomesEvenOddDerivativeMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h01.symm
  · rintro ⟨h10, h11⟩
    apply Matrix.ext
    intro i j
    revert i j
    simp [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      gomesEvenOddDerivativeMatrix, h10, h11, mul_comm]

/-- A residue subsequence of formal coefficients, without any convergence requirement. -/
def gomesFormalCoefficientResidue (m : ℕ) (j : Fin m) (F : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => PowerSeries.coeff (n * m + j.val) F

/-- Every formal function of differentiation has its exact even-odd companion matrix. -/
theorem gomesFormalSeriesDerivativePowerMatrixHom_two (F : PowerSeries K) :
    gomesFormalSeriesDerivativePowerMatrixHom K 2 F =
      !![gomesFormalCoefficientResidue K 2 0 F, gomesFormalCoefficientResidue K 2 1 F;
        PowerSeries.X * gomesFormalCoefficientResidue K 2 1 F,
        gomesFormalCoefficientResidue K 2 0 F] := by
  let M := gomesFormalSeriesDerivativePowerMatrixHom K 2 F
  have h0 (j : Fin 2) : M 0 j = gomesFormalCoefficientResidue K 2 j F := by
    apply PowerSeries.ext
    intro n
    exact (gomesFormalSeriesDerivativePowerMatrixHom_first_row K 2 F j n).trans
      (PowerSeries.coeff_mk n (fun n => PowerSeries.coeff (n * 2 + j.val) F)).symm
  have hcomm : Commute M (gomesEvenOddDerivativeMatrix K) := by
    rw [← gomesFormalSeriesDerivativePowerMatrixHom_two_X]
    exact (Commute.all F PowerSeries.X).map (gomesFormalSeriesDerivativePowerMatrixHom K 2)
  obtain ⟨h10, h11⟩ := (gomesEvenOddDerivativeMatrix_commutes_iff K M).mp hcomm
  change M = _
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, h10, h11, h0]

end GaloisForLFunctions.HTGeometry
