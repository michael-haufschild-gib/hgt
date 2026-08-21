import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitPauliTransport

/-!
# Pauli-Clifford closure for Haferkamp two-qubit transport

The local gates selected in the light-cone transport must preserve the entire
Pauli family, not only the Pauli string they merge.  This file gives compact
symbolic action tables for the Boolean CNOT and SWAP seeds and closes them
under tensor products and gate multiplication.
-/

open Matrix
open scoped Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A one-qubit unitary normalizes the literal Boolean Pauli family. -/
def IsBoolOneQubitPauliClifford (U : Matrix Bool Bool ℂ) : Prop :=
  ∀ p : Option (Fin 3), ∃ c : ℂ, ∃ q : Option (Fin 3), c ≠ 0 ∧
    U * boolPauliOption p * Matrix.conjTranspose U = c • boolPauliOption q

/-- A two-qubit unitary normalizes the literal Boolean Pauli family. -/
def IsBoolTwoQubitPauliClifford (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Prop :=
  ∀ p q : Option (Fin 3), ∃ c : ℂ, ∃ r s : Option (Fin 3), c ≠ 0 ∧
    U * boolTwoQubitPauli p q * Matrix.conjTranspose U = c • boolTwoQubitPauli r s

private theorem boolHadamard_conj_Y :
    (boolHadamard : Matrix Bool Bool ℂ) * finiteQubitPauli 1 *
        Matrix.conjTranspose (boolHadamard : Matrix Bool Bool ℂ) = -finiteQubitPauli 1 := by
  have hsqrt : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [boolHadamard, boolHadamardMatrix, finiteQubitPauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    field_simp <;> rw [hsqrt] <;> ring

private theorem boolHadamard_conj_Z :
    (boolHadamard : Matrix Bool Bool ℂ) * finiteQubitPauli 2 *
        Matrix.conjTranspose (boolHadamard : Matrix Bool Bool ℂ) = finiteQubitPauli 0 := by
  have hsqrt : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [boolHadamard, boolHadamardMatrix, finiteQubitPauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    field_simp <;> rw [hsqrt] <;> ring

private theorem boolPhase_conj_X :
    (boolPhase : Matrix Bool Bool ℂ) * finiteQubitPauli 0 *
        Matrix.conjTranspose (boolPhase : Matrix Bool Bool ℂ) = finiteQubitPauli 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [boolPhase, boolPhaseMatrix, finiteQubitPauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem boolPhase_conj_Z :
    (boolPhase : Matrix Bool Bool ℂ) * finiteQubitPauli 2 *
        Matrix.conjTranspose (boolPhase : Matrix Bool Bool ℂ) = finiteQubitPauli 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [boolPhase, boolPhaseMatrix, finiteQubitPauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The CNOT Pauli output-label table in the Boolean convention. -/
def boolTwoQubitCNOTTarget : Option (Fin 3) → Option (Fin 3) →
    Option (Fin 3) × Option (Fin 3)
  | none, none => (none, none)
  | none, some 0 => (none, some 0)
  | none, some 1 => (some 2, some 1)
  | none, some 2 => (some 2, some 2)
  | some 0, none => (some 0, some 0)
  | some 0, some 0 => (some 0, none)
  | some 0, some 1 => (some 1, some 2)
  | some 0, some 2 => (some 1, some 1)
  | some 1, none => (some 1, some 0)
  | some 1, some 0 => (some 1, none)
  | some 1, some 1 => (some 0, some 2)
  | some 1, some 2 => (some 0, some 1)
  | some 2, none => (some 2, none)
  | some 2, some 0 => (some 2, some 0)
  | some 2, some 1 => (none, some 1)
  | some 2, some 2 => (none, some 2)

/-- The CNOT Pauli phase table in the Boolean convention. -/
def boolTwoQubitCNOTScalar : Option (Fin 3) → Option (Fin 3) → ℂ
  | some 0, some 2 => -1
  | some 1, some 1 => -1
  | _, _ => 1

private theorem boolTwoQubitCNOT_conj_none_none :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli none none *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli none none := by
  rw [boolTwoQubitPauli, boolPauliOption]
  simp only [Matrix.kronecker_one, Matrix.mul_one]
  exact mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.mp boolTwoQubitCNOT.2)

private theorem boolTwoQubitCNOT_conj_none_X :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli none (some 0) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli none (some 0) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_none_Y :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli none (some 1) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 2) (some 1) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_none_Z :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli none (some 2) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 2) (some 2) :=
  boolTwoQubitCNOT_conj_targetZ

private theorem boolTwoQubitCNOT_conj_X_none :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 0) none *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 0) (some 0) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_X_X :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 0) (some 0) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 0) none := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_X_Y :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 0) (some 1) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 1) (some 2) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_X_Z :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 0) (some 2) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      (-1 : ℂ) • boolTwoQubitPauli (some 1) (some 1) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_Y_none :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 1) none *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 1) (some 0) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_Y_X :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 1) (some 0) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 1) none := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_Y_Y :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 1) (some 1) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      (-1 : ℂ) • boolTwoQubitPauli (some 0) (some 2) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_Y_Z :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 1) (some 2) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 0) (some 1) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_Z_none :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 2) none *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 2) none := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_Z_X :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 2) (some 0) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 2) (some 0) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_Z_Y :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 2) (some 1) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli none (some 1) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

private theorem boolTwoQubitCNOT_conj_Z_Z :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 2) (some 2) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli none (some 2) :=
  boolTwoQubitCNOT_conj_twoZ

/-- Symbolic CNOT action on all sixteen two-qubit Pauli labels. -/
theorem boolTwoQubitCNOT_conj_boolTwoQubitPauli
    (p q : Option (Fin 3)) :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli p q *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitCNOTScalar p q •
        boolTwoQubitPauli (boolTwoQubitCNOTTarget p q).1
          (boolTwoQubitCNOTTarget p q).2 := by
  fin_cases p <;> fin_cases q <;>
    simp only [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget, one_smul] <;>
    first
    | exact boolTwoQubitCNOT_conj_none_none
    | exact boolTwoQubitCNOT_conj_none_X
    | exact boolTwoQubitCNOT_conj_none_Y
    | exact boolTwoQubitCNOT_conj_none_Z
    | exact boolTwoQubitCNOT_conj_X_none
    | exact boolTwoQubitCNOT_conj_X_X
    | exact boolTwoQubitCNOT_conj_X_Y
    | exact boolTwoQubitCNOT_conj_X_Z
    | exact boolTwoQubitCNOT_conj_Y_none
    | exact boolTwoQubitCNOT_conj_Y_X
    | exact boolTwoQubitCNOT_conj_Y_Y
    | exact boolTwoQubitCNOT_conj_Y_Z
    | exact boolTwoQubitCNOT_conj_Z_none
    | exact boolTwoQubitCNOT_conj_Z_X
    | exact boolTwoQubitCNOT_conj_Z_Y
    | exact boolTwoQubitCNOT_conj_Z_Z

end

end GaloisForLFunctions.HTGeometry
