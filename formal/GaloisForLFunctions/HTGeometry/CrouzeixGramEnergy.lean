import GaloisForLFunctions.HTGeometry.FiniteNuclearIncidenceLaw

/-!
# Exact positive-block energy for rectangular Gram matrices

The positive-block comparison in §3 of *A direct proof of the complete Crouzeix inequality*
bounds twice the off-diagonal Hilbert--Schmidt energy by the two diagonal energies.
For a Gram block built from arbitrary rectangular matrices, its deficit is exactly the
Hilbert--Schmidt square of the difference of their source covariance matrices. Consequently
saturation means equality of covariances, even when the column counts differ or ranks vanish.
-/

open Matrix
open scoped BigOperators ComplexConjugate Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {h x y : Type*} [Fintype h] [Fintype x] [Fintype y]
  [DecidableEq h] [DecidableEq x] [DecidableEq y]

omit [DecidableEq x] in
/-- Hilbert--Schmidt square is nonnegative, including for empty rectangular matrices. -/
theorem finiteMatrixHilbertSchmidtSq_nonneg (A : Matrix x y ℂ) :
    0 ≤ finiteMatrixHilbertSchmidtSq A := by
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

omit [DecidableEq x] in
/-- Vanishing Hilbert--Schmidt square detects the whole matrix. -/
@[simp] theorem finiteMatrixHilbertSchmidtSq_eq_zero_iff (A : Matrix x y ℂ) :
    finiteMatrixHilbertSchmidtSq A = 0 ↔ A = 0 := by
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  simp only [Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (‖A i j‖)), Finset.mem_univ, forall_const,
    Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _),
    sq_eq_zero_iff, norm_eq_zero, Matrix.ext_iff]
  rfl

/-- Adjoints preserve Hilbert--Schmidt square. -/
@[simp] theorem finiteMatrixHilbertSchmidtSq_conjTranspose (A : Matrix x y ℂ) :
    finiteMatrixHilbertSchmidtSq Aᴴ = finiteMatrixHilbertSchmidtSq A := by
  simp only [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq,
    Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

/-- Source and target Gram matrices have identical quadratic energy. -/
theorem finiteMatrixHilbertSchmidtSq_gram_duality (A : Matrix h x ℂ) :
    finiteMatrixHilbertSchmidtSq (Aᴴ * A) =
      finiteMatrixHilbertSchmidtSq (A * Aᴴ) := by
  simp only [finiteMatrixHilbertSchmidtSq, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm Aᴴ]
  simp only [Matrix.mul_assoc]

omit [DecidableEq h] [DecidableEq x] in
/-- Cross-Gram collision energy is the trace pairing of the two source covariances. -/
theorem finiteMatrixHilbertSchmidtSq_cross_gram (A : Matrix h x ℂ) (B : Matrix h y ℂ) :
    finiteMatrixHilbertSchmidtSq (Aᴴ * B) =
      (Matrix.trace ((A * Aᴴ) * (B * Bᴴ))).re := by
  simp only [finiteMatrixHilbertSchmidtSq, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm Bᴴ]
  simp only [Matrix.mul_assoc]

/-- The exact positive-block deficit is a covariance distance, without rank assumptions. -/
theorem crouzeix_gram_energy_identity (A : Matrix h x ℂ) (B : Matrix h y ℂ) :
    finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B) =
      finiteMatrixHilbertSchmidtSq (A * Aᴴ - B * Bᴴ) := by
  rw [finiteMatrixHilbertSchmidtSq_gram_duality A,
    finiteMatrixHilbertSchmidtSq_gram_duality B,
    finiteMatrixHilbertSchmidtSq_cross_gram]
  simp only [finiteMatrixHilbertSchmidtSq, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [Matrix.trace_mul_comm (B * Bᴴ) (A * Aᴴ)]
  ring

/-- Rectangular Gram blocks satisfy the positive-block comparison with no positivity premise. -/
theorem crouzeix_gram_energy_bound (A : Matrix h x ℂ) (B : Matrix h y ℂ) :
    2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B) ≤
      finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) := by
  have hid := crouzeix_gram_energy_identity A B
  have hpos := finiteMatrixHilbertSchmidtSq_nonneg (A * Aᴴ - B * Bᴴ)
  linarith

/-- Saturation detects equality of source covariances, not equality of feature labels. -/
theorem crouzeix_gram_energy_saturation (A : Matrix h x ℂ) (B : Matrix h y ℂ) :
    2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B) =
        finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) ↔
      A * Aᴴ = B * Bᴴ := by
  have hid := crouzeix_gram_energy_identity A B
  constructor
  · intro he
    apply sub_eq_zero.mp
    apply (finiteMatrixHilbertSchmidtSq_eq_zero_iff _).mp
    linarith
  · intro he
    have hz := (finiteMatrixHilbertSchmidtSq_eq_zero_iff _).mpr (sub_eq_zero.mpr he)
    linarith

/-- The entire entrywise covariance discrepancy is controlled by the positive-block deficit. -/
theorem crouzeix_gram_energy_entry_bound (A : Matrix h x ℂ) (B : Matrix h y ℂ) (i j : h) :
    ‖(A * Aᴴ) i j - (B * Bᴴ) i j‖ ^ 2 ≤
      finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B) := by
  rw [crouzeix_gram_energy_identity, finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  exact le_trans
    (Finset.single_le_sum (fun k _ => sq_nonneg ‖(A * Aᴴ - B * Bᴴ) i k‖)
      (Finset.mem_univ j))
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ =>
      sq_nonneg ‖(A * Aᴴ - B * Bᴴ) k l‖)
      (Finset.mem_univ i))

end

end GaloisForLFunctions.HTGeometry
