import GaloisForLFunctions.QuantumAlg.Util.MatrixExpInvolution
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.BipartiteMatrixDecomposition
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.NoncommRing

/-!
# Interaction cross-fibre witnesses

Exact involution-conjugation law underlying the two-qubit interaction witness from the passive
triangle and resource-filtered relation cards.
-/

namespace HTGeometry.ConstraintRelativity

open scoped ComplexConjugate

section Involution

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Exponential of a complex-scaled involution. -/
theorem exp_I_smul_involution (H : A) (hH : H * H = 1) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • H) =
      (Real.cos t : ℂ) • (1 : A) + (Complex.I * (Real.sin t : ℂ)) • H := by
  have hcosh : Complex.cosh (Complex.I * (t : ℂ)) = (Real.cos t : ℂ) := by
    rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring,
      Complex.cosh_mul_I, ← Complex.ofReal_cos]
  have hsinh : Complex.sinh (Complex.I * (t : ℂ)) =
      Complex.I * (Real.sin t : ℂ) := by
    rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring,
      Complex.sinh_mul_I, ← Complex.ofReal_sin]
    ring
  rw [hcosh.symm, hsinh.symm]
  exact QuantumAlg.exp_smul_of_mul_self_eq_one (Complex.I * (t : ℂ)) hH

/-- Algebraic core of involution conjugation. -/
theorem involution_conjugation_identity (H O : A) (hH : H * H = 1)
    (hanti : H * O = -(O * H)) (c d : ℂ) :
    (c • (1 : A) + d • H) * O * (c • (1 : A) - d • H) =
      (c ^ (2 : ℕ) + d ^ (2 : ℕ)) • O + (2 * c * d) • (H * O) := by
  have hOH : O * H = -(H * O) := by rw [hanti, neg_neg]
  have hHOH : H * (O * H) = -O := by
    rw [hOH, mul_neg, ← mul_assoc, hH, one_mul]
  calc (c • (1 : A) + d • H) * O * (c • (1 : A) - d • H)
      = (c • O + d • (H * O)) * (c • (1 : A) - d • H) := by
        rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
    _ = (c ^ (2 : ℕ) + d ^ (2 : ℕ)) • O + (2 * c * d) • (H * O) := by
        simp only [mul_sub, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, smul_smul,
          mul_assoc]
        rw [hHOH, hOH]
        module

/-- Exact conjugation law for an involution acting on an anticommuting reporter. -/
theorem conjugation_of_involution_anticommute (H O : A) (hH : H * H = 1)
    (hanti : H * O = -(O * H)) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * O *
        NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H) =
      (Real.cos (2 * t) : ℂ) • O +
        (Complex.I * (Real.sin (2 * t) : ℂ)) • (H * O) := by
  rw [exp_I_smul_involution H hH t]
  have hneg : (-(Complex.I * (t : ℂ))) = Complex.I * ((-t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hneg, exp_I_smul_involution H hH (-t), Real.cos_neg, Real.sin_neg]
  rw [Complex.ofReal_neg, mul_neg, neg_smul, ← sub_eq_add_neg,
    involution_conjugation_identity H O hH hanti]
  apply congrArg₂ (· + ·)
  · congr 1
    push_cast
    rw [Complex.cos_two_mul']
    linear_combination (Complex.sin (t : ℂ) ^ (2 : ℕ)) * Complex.I_sq
  · congr 1
    push_cast
    rw [Complex.sin_two_mul]
    ring

end Involution

/-! ## Two-qubit Pauli exposure -/

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev TwoQubitMatrix := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

def pauliX : QubitMatrix := !![0, 1; 1, 0]
def pauliY : QubitMatrix := !![0, -Complex.I; Complex.I, 0]
def pauliZ : QubitMatrix := !![1, 0; 0, -1]

@[simp] theorem pauliX_trace : pauliX.trace = 0 := by
  norm_num [pauliX, Matrix.trace, Fin.sum_univ_two]

@[simp] theorem pauliY_trace : pauliY.trace = 0 := by
  norm_num [pauliY, Matrix.trace, Fin.sum_univ_two]

@[simp] theorem pauliZ_trace : pauliZ.trace = 0 := by
  norm_num [pauliZ, Matrix.trace, Fin.sum_univ_two]

/-- The oriented interaction term is invisible to both boundary partial traces. -/
theorem pauliY_kronecker_pauliZ_mem_cross :
    Matrix.kronecker pauliY pauliZ ∈
      matrixCrossFibre (m := Fin 2) (n := Fin 2) := by
  exact kronecker_mem_matrixCrossFibre pauliY_trace pauliZ_trace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Cards Passive 5.3 / Resource 5.4.** The `Z ⊗ Z` interaction sends local `X ⊗ I` into the
oriented cross-fibre `Y ⊗ Z` with exact sine coefficient. -/
theorem twoQubit_ZZ_exposure (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • Matrix.kronecker pauliZ pauliZ) *
        Matrix.kronecker pauliX (1 : QubitMatrix) *
        NormedSpace.exp ((-(Complex.I * (t : ℂ))) • Matrix.kronecker pauliZ pauliZ) =
      (Real.cos (2 * t) : ℂ) • Matrix.kronecker pauliX (1 : QubitMatrix) -
        (Real.sin (2 * t) : ℂ) • Matrix.kronecker pauliY pauliZ := by
  have hH : Matrix.kronecker pauliZ pauliZ * Matrix.kronecker pauliZ pauliZ =
      (1 : TwoQubitMatrix) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [pauliZ, Matrix.kronecker_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hanti :
      Matrix.kronecker pauliZ pauliZ * Matrix.kronecker pauliX (1 : QubitMatrix) =
        -(Matrix.kronecker pauliX (1 : QubitMatrix) * Matrix.kronecker pauliZ pauliZ) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [pauliX, pauliZ, Matrix.kronecker_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hconj := conjugation_of_involution_anticommute
    (Matrix.kronecker pauliZ pauliZ) (Matrix.kronecker pauliX (1 : QubitMatrix)) hH hanti t
  refine hconj.trans ?_
  have hprod :
      Matrix.kronecker pauliZ pauliZ * Matrix.kronecker pauliX (1 : QubitMatrix) =
        Complex.I • Matrix.kronecker pauliY pauliZ := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [pauliX, pauliY, pauliZ, Matrix.kronecker_apply, Matrix.mul_apply,
        Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [hprod, smul_smul, sub_eq_add_neg, ← neg_smul]
  have hscalar : Complex.I * ((Real.sin (2 * t) : ℝ) : ℂ) * Complex.I
      = -((Real.sin (2 * t) : ℝ) : ℂ) := by
    linear_combination ((Real.sin (2 * t) : ℝ) : ℂ) * Complex.I_sq
  rw [hscalar]

end HTGeometry.ConstraintRelativity
