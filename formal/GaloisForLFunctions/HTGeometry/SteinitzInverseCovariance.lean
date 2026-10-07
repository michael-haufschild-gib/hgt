import GaloisForLFunctions.HTGeometry.CrouzeixGramEnergy
import GaloisForLFunctions.HTGeometry.FiniteBuresReporterVariationalLaw

/-!
# The Steinitz inverse-potential remainder on regularized covariances

The source `openai/math/lean/OAI/Analysis/Steinitz/MatrixEnergy.lean` proves
`potential_large` and defines `scalarRemainder`. On its inverse branch the
remainder is an exact rational square. Here that algebra is lifted to
noncommuting complex covariance matrices using the corpus's existing positive
regularization. The matrix remainder is positive, splits into two squared
Hilbert--Schmidt norms, and vanishes exactly at covariance equality.

This is an application of the inverse branch, not a port of the full Steinitz
signing theorem or its other potential branches.
-/

open Matrix
open scoped Matrix MatrixOrder ComplexOrder NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The inverse branch of the scalar remainder in the Steinitz matrix-energy argument. -/
def steinitzInverseBranchRemainder (x y : ℝ) : ℝ :=
  (5 / 3 - x⁻¹) - (5 / 3 - y⁻¹) + (y / x - 1) * (x⁻¹ + y⁻¹) / 2

/-- On regularized nonnegative data the scalar remainder is an exact positive square. -/
theorem steinitzInverseBranchRemainder_regularized (r s : ℝ≥0) :
    steinitzInverseBranchRemainder (1 + r) (1 + s) =
      ((r : ℝ) - s) ^ 2 / (2 * (1 + r) ^ 2 * (1 + s)) := by
  have hr : (1 : ℝ) + r ≠ 0 := ne_of_gt (by positivity)
  have hs : (1 : ℝ) + s ≠ 0 := ne_of_gt (by positivity)
  unfold steinitzInverseBranchRemainder
  field_simp [hr, hs]
  ring

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Existing positive regularization, specialized to an arbitrary synthesis covariance. -/
abbrev synthesisRegularizedCovariance (A : Matrix (Fin d) ι ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  finitePositiveMatrixRegularization (A * Aᴴ) 1

@[simp] theorem synthesisRegularizedCovariance_eq (A : Matrix (Fin d) ι ℂ) :
    synthesisRegularizedCovariance A = A * Aᴴ + 1 := by
  simp only [synthesisRegularizedCovariance, finitePositiveMatrixRegularization, one_smul]

theorem synthesisRegularizedCovariance_posDef (A : Matrix (Fin d) ι ℂ) :
    (synthesisRegularizedCovariance A).PosDef :=
  finitePositiveMatrixRegularization_posDef (posSemidef_self_mul_conjTranspose A) zero_lt_one

/-- Inverse covariance exists even for dependent or empty synthesis families. -/
def synthesisResolvent (A : Matrix (Fin d) ι ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (synthesisRegularizedCovariance A)⁻¹

/-- Matrix lift of twice the inverse-branch scalar remainder. -/
def synthesisInverseRemainder (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin d) κ ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  synthesisResolvent B - synthesisResolvent A -
    synthesisResolvent A * (synthesisRegularizedCovariance A -
      synthesisRegularizedCovariance B) * synthesisResolvent A

/-- The inverse tangent error is a positive congruence, including noncommuting covariances. -/
theorem synthesisInverseRemainder_factorization
    (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin d) κ ℂ) :
    synthesisInverseRemainder A B =
      (synthesisResolvent A - synthesisResolvent B)ᴴ *
        synthesisRegularizedCovariance B * (synthesisResolvent A - synthesisResolvent B) := by
  letI := (synthesisRegularizedCovariance_posDef A).isUnit.invertible
  letI := (synthesisRegularizedCovariance_posDef B).isUnit.invertible
  have hA := (synthesisRegularizedCovariance_posDef A).isHermitian.inv
  have hB := (synthesisRegularizedCovariance_posDef B).isHermitian.inv
  simp only [synthesisInverseRemainder, synthesisResolvent, conjTranspose_sub, hA.eq, hB.eq,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
    Matrix.mul_inv_of_invertible, Matrix.one_mul, Matrix.mul_one]
  abel

/-- The source's inverse-branch remainder stays positive after lifting to complex matrices. -/
theorem synthesisInverseRemainder_posSemidef
    (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin d) κ ℂ) :
    (synthesisInverseRemainder A B).PosSemidef := by
  rw [synthesisInverseRemainder_factorization]
  exact (synthesisRegularizedCovariance_posDef B).posSemidef.conjTranspose_mul_mul_same _

/-- Exact inverse stability: the trace remainder splits into two squared matrix norms. -/
theorem synthesisInverseRemainder_trace_identity
    (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin d) κ ℂ) :
    (synthesisInverseRemainder A B).trace.re =
      finiteMatrixHilbertSchmidtSq (synthesisResolvent A - synthesisResolvent B) +
      finiteMatrixHilbertSchmidtSq (Bᴴ * (synthesisResolvent A - synthesisResolvent B)) := by
  have hH : (synthesisResolvent A - synthesisResolvent B).IsHermitian :=
    (synthesisRegularizedCovariance_posDef A).isHermitian.inv.sub
      (synthesisRegularizedCovariance_posDef B).isHermitian.inv
  rw [synthesisInverseRemainder_factorization, synthesisRegularizedCovariance_eq, hH.eq]
  simp only [finiteMatrixHilbertSchmidtSq, conjTranspose_mul, conjTranspose_conjTranspose,
    hH.eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.trace_add, Complex.add_re,
    Matrix.mul_assoc]
  exact add_comm _ _

/-- The trace remainder controls the full inverse-covariance discrepancy. -/
theorem synthesisResolvent_distance_bound
    (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin d) κ ℂ) :
    finiteMatrixHilbertSchmidtSq (synthesisResolvent A - synthesisResolvent B) ≤
      (synthesisInverseRemainder A B).trace.re := by
  rw [synthesisInverseRemainder_trace_identity]
  exact le_add_of_nonneg_right (finiteMatrixHilbertSchmidtSq_nonneg _)

/-- Every inverse-covariance entry is controlled by the same trace remainder. -/
theorem synthesisResolvent_entry_bound
    (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin d) κ ℂ) (i j : Fin d) :
    ‖synthesisResolvent A i j - synthesisResolvent B i j‖ ^ 2 ≤
      (synthesisInverseRemainder A B).trace.re := by
  apply le_trans _ (synthesisResolvent_distance_bound A B)
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  exact le_trans
    (Finset.single_le_sum (fun k _ =>
      sq_nonneg ‖(synthesisResolvent A - synthesisResolvent B) i k‖) (Finset.mem_univ j))
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ =>
      sq_nonneg ‖(synthesisResolvent A - synthesisResolvent B) k l‖) (Finset.mem_univ i))

/-- Zero remainder detects covariance equality without a rank or spectral-gap assumption. -/
theorem synthesisInverseRemainder_trace_eq_zero_iff
    (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin d) κ ℂ) :
    (synthesisInverseRemainder A B).trace.re = 0 ↔ A * Aᴴ = B * Bᴴ := by
  constructor
  · intro hz
    have hs : finiteMatrixHilbertSchmidtSq (synthesisResolvent A - synthesisResolvent B) = 0 :=
      le_antisymm (hz ▸ synthesisResolvent_distance_bound A B)
        (finiteMatrixHilbertSchmidtSq_nonneg _)
    have he : synthesisResolvent A = synthesisResolvent B :=
      sub_eq_zero.mp ((finiteMatrixHilbertSchmidtSq_eq_zero_iff _).mp hs)
    letI := (synthesisRegularizedCovariance_posDef A).isUnit.invertible
    letI := (synthesisRegularizedCovariance_posDef B).isUnit.invertible
    have hi := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M⁻¹) he
    change (synthesisRegularizedCovariance A)⁻¹⁻¹ =
      (synthesisRegularizedCovariance B)⁻¹⁻¹ at hi
    rw [Matrix.inv_inv_of_invertible, Matrix.inv_inv_of_invertible] at hi
    simpa only [synthesisRegularizedCovariance_eq, add_left_inj] using hi
  · intro h
    have he : synthesisRegularizedCovariance A = synthesisRegularizedCovariance B := by
      simpa only [synthesisRegularizedCovariance_eq, add_left_inj] using h
    have hi : synthesisResolvent A = synthesisResolvent B := congrArg Inv.inv he
    simp only [synthesisInverseRemainder_factorization, hi, sub_self, conjTranspose_zero,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

end

end GaloisForLFunctions.HTGeometry
