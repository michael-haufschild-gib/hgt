import GaloisForLFunctions.RHTower.CCM.CCMDiagonalFockLift
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseInfiniteFockKernel

/-!
# Explicit inverse Jordan averaging

For the strictly positive diagonal `Dᵢᵢ = exp(rᵢ)`, the equation
`(D X + X D)/2 = A` has the unique solution `Xᵢⱼ = 2 Aᵢⱼ/(Dᵢᵢ+Dⱼⱼ)`.
The inverse is a Cauchy Schur multiplier and therefore preserves positivity.

This is the diagonal Sylvester mechanism of Hoogsteder-Riera,
*The cone of states over time*, Proposition 2.3.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.CauchyJordan

/-- Strictly positive rates, parametrized without a positivity premise. -/
def rate {n : ℕ} (r : Fin n → ℝ) (i : Fin n) : ℝ := Real.exp (r i)

/-- Jordan multiplication by a positive diagonal. -/
def jordan {n : ℕ} (r : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (diagonal (fun i => (rate r i : ℂ)) * A +
    A * diagonal (fun i => (rate r i : ℂ)))

/-- Inverse Jordan multiplier, given entrywise by a Cauchy kernel. -/
def inverseJordan {n : ℕ} (r : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => 2 * A i j / ((rate r i : ℂ) + (rate r j : ℂ))

theorem rate_pos {n : ℕ} (r : Fin n → ℝ) (i : Fin n) : 0 < rate r i :=
  Real.exp_pos _

/-- Complex Cauchy matrix associated with the positive rates. -/
def cauchySymbol {n : ℕ} (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (RHTower.kernelMatrix RHTower.cauchyKernel (rate r)).map (algebraMap ℝ ℂ)

theorem cauchySymbol_posSemidef {n : ℕ} (r : Fin n → ℝ) :
    (cauchySymbol r).PosSemidef :=
  _root_.RHTower.realMatrix_posSemidef_map_complex _
    (RHTower.posSemidef_cauchyMatrix (rate_pos r))

private theorem rate_sum_ne {n : ℕ} (r : Fin n → ℝ) (i j : Fin n) :
    (rate r i : ℂ) + (rate r j : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_add]
  exact Complex.ofReal_ne_zero.mpr (add_pos (rate_pos r i) (rate_pos r j)).ne'

theorem jordan_apply {n : ℕ} (r : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : jordan r A i j = ((rate r i : ℂ) + (rate r j : ℂ)) * A i j / 2 := by
  simp only [jordan, Matrix.smul_apply, Matrix.add_apply, diagonal_mul, mul_diagonal,
    smul_eq_mul]
  ring

/-- Inverse Jordan averaging solves the equation at every matrix, including indefinite ones. -/
theorem jordan_inverseJordan {n : ℕ} (r : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    jordan r (inverseJordan r A) = A := by
  ext i j
  rw [jordan_apply, inverseJordan]
  field_simp [rate_sum_ne r i j]

/-- The explicit solver is also a left inverse. -/
theorem inverseJordan_jordan {n : ℕ} (r : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    inverseJordan r (jordan r A) = A := by
  ext i j
  rw [inverseJordan, jordan_apply]
  field_simp [rate_sum_ne r i j]

/-- Every prescribed matrix has exactly one Jordan preimage. -/
theorem jordan_solution_iff {n : ℕ} (r : Fin n → ℝ)
    (X A : Matrix (Fin n) (Fin n) ℂ) :
    jordan r X = A ↔ X = inverseJordan r A := by
  constructor
  · intro h
    rw [← inverseJordan_jordan r X, h]
  · rintro rfl
    exact jordan_inverseJordan r A

/-- The inverse multiplier is precisely twice the positive Cauchy kernel. -/
theorem inverseJordan_eq_hadamard {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    inverseJordan r A =
      (2 : ℂ) • (A ⊙ cauchySymbol r) := by
  ext i j
  change 2 * A i j / ((rate r i : ℂ) + (rate r j : ℂ)) =
    2 * (A i j * ((1 / (rate r i + rate r j) : ℝ) : ℂ))
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add]
  ring

/-- Every Gram matrix has a positive inverse Jordan image; positivity is constructed. -/
theorem inverseJordan_gram_posSemidef {n m : ℕ} (r : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin n) ℂ) : (inverseJordan r (Bᴴ * B)).PosSemidef := by
  rw [inverseJordan_eq_hadamard]
  exact ((posSemidef_conjTranspose_mul_self B).hadamard (cauchySymbol_posSemidef r)).smul
    (by norm_num : 0 ≤ (2 : ℂ))

/-- Transposition commutes with inverse Jordan averaging. -/
theorem inverseJordan_transpose {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : inverseJordan r Aᵀ = (inverseJordan r A)ᵀ := by
  ext i j
  simp only [inverseJordan, transpose_apply, add_comm]

/-- The weighted trace of the solution recovers the trace of the prescribed matrix. -/
theorem trace_diagonal_mul_inverseJordan {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    trace (diagonal (fun i => (rate r i : ℂ)) * inverseJordan r A) = trace A := by
  unfold trace
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonal_mul, inverseJordan]
  field_simp [rate_sum_ne r i i]
  ring

/-- The inverse is linear in the prescribed data. -/
theorem inverseJordan_add_smul {n : ℕ} (r : Fin n → ℝ)
    (A B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    inverseJordan r (A + c • B) = inverseJordan r A + c • inverseJordan r B := by
  ext i j
  simp only [inverseJordan, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem inverseJordan_sub {n : ℕ} (r : Fin n → ℝ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    inverseJordan r (A - B) = inverseJordan r A - inverseJordan r B := by
  ext i j
  simp only [inverseJordan, Matrix.sub_apply]
  ring

/-- The same multiplier acts on the first factor of an arbitrary finite auxiliary system. -/
def amplifiedInverseJordan {n m : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  fun i j => 2 * A i j / ((rate r i.1 : ℂ) + (rate r j.1 : ℂ))

/-- Positivity survives every auxiliary dimension: the inverse Jordan map is completely positive.
The input is an arbitrary square factor, so every positivity premise is discharged. -/
theorem amplifiedInverseJordan_gram_posSemidef {n m k : ℕ} (r : Fin n → ℝ)
    (B : Matrix (Fin k) (Fin n × Fin m) ℂ) :
    (amplifiedInverseJordan r (Bᴴ * B)).PosSemidef := by
  have heq : amplifiedInverseJordan r (Bᴴ * B) =
      (2 : ℂ) • ((Bᴴ * B) ⊙ (cauchySymbol r).submatrix Prod.fst Prod.fst) := by
    ext i j
    change 2 * (Bᴴ * B) i j / ((rate r i.1 : ℂ) + (rate r j.1 : ℂ)) =
      2 * ((Bᴴ * B) i j * ((1 / (rate r i.1 + rate r j.1) : ℝ) : ℂ))
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add]
    ring
  rw [heq]
  exact ((posSemidef_conjTranspose_mul_self B).hadamard
    ((cauchySymbol_posSemidef r).submatrix Prod.fst)).smul (by norm_num : 0 ≤ (2 : ℂ))

/-- Transposing only the first factor commutes with the amplified inverse. -/
theorem amplifiedInverseJordan_partialTranspose {n m : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    amplifiedInverseJordan r (fun i j => A (j.1, i.2) (i.1, j.2)) =
      fun i j => amplifiedInverseJordan r A (j.1, i.2) (i.1, j.2) := by
  ext i j
  simp only [amplifiedInverseJordan, add_comm]

/-- Taking a partial trace gives the inverse Jordan map on the remaining factor. -/
theorem amplifiedInverseJordan_partialTrace {n m : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    (fun i j => ∑ a : Fin m, amplifiedInverseJordan r A (i, a) (j, a)) =
      inverseJordan r (fun i j => ∑ a : Fin m, A (i, a) (j, a)) := by
  ext i j
  simp only [amplifiedInverseJordan, inverseJordan, Finset.sum_div, Finset.mul_sum]

#print axioms jordan_solution_iff
#print axioms inverseJordan_gram_posSemidef
#print axioms inverseJordan_transpose
#print axioms trace_diagonal_mul_inverseJordan
#print axioms inverseJordan_add_smul
#print axioms amplifiedInverseJordan_gram_posSemidef
#print axioms amplifiedInverseJordan_partialTranspose
#print axioms amplifiedInverseJordan_partialTrace

end GaloisForLFunctions.HilbertMetric.CauchyJordan
