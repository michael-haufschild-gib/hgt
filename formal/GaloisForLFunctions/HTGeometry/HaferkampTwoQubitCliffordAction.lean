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
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.kronecker, Bool.xor]

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
  fin_cases p
  · fin_cases q
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_none_none
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_none_X
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_none_Y
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_none_Z
  · fin_cases q
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_X_none
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_X_X
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_X_Y
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_X_Z
  · fin_cases q
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_Y_none
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_Y_X
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_Y_Y
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_Y_Z
  · fin_cases q
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_Z_none
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_Z_X
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_Z_Y
    · simpa [boolTwoQubitCNOTScalar, boolTwoQubitCNOTTarget] using
        boolTwoQubitCNOT_conj_Z_Z

theorem isBoolOneQubitPauliClifford_mul
    (U V : Matrix.unitaryGroup Bool ℂ)
    (hU : IsBoolOneQubitPauliClifford (U : Matrix Bool Bool ℂ))
    (hV : IsBoolOneQubitPauliClifford (V : Matrix Bool Bool ℂ)) :
    IsBoolOneQubitPauliClifford ((U * V : Matrix.unitaryGroup Bool ℂ) : Matrix Bool Bool ℂ) := by
  intro p
  obtain ⟨cV, q, hcV, hVq⟩ := hV p
  obtain ⟨cU, r, hcU, hUr⟩ := hU q
  refine ⟨cV * cU, r, mul_ne_zero hcV hcU, ?_⟩
  rw [unitary_mul_conjugation_smul U V _ _ _ hVq, hUr, smul_smul]

theorem boolHadamard_isBoolOneQubitPauliClifford :
    IsBoolOneQubitPauliClifford (boolHadamard : Matrix Bool Bool ℂ) := by
  intro p
  fin_cases p
  · refine ⟨1, none, one_ne_zero, ?_⟩
    simp only [boolPauliOption, Matrix.mul_one, one_smul]
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp boolHadamard.2
  · exact ⟨1, some 2, one_ne_zero, by
      simpa [boolPauliOption] using boolHadamard_conj_X⟩
  · exact ⟨-1, some 1, neg_ne_zero.mpr one_ne_zero, by
      simpa [boolPauliOption] using boolHadamard_conj_Y⟩
  · exact ⟨1, some 0, one_ne_zero, by
      simpa [boolPauliOption] using boolHadamard_conj_Z⟩

theorem boolPhase_isBoolOneQubitPauliClifford :
    IsBoolOneQubitPauliClifford (boolPhase : Matrix Bool Bool ℂ) := by
  intro p
  fin_cases p
  · refine ⟨1, none, one_ne_zero, ?_⟩
    simp only [boolPauliOption, Matrix.mul_one, one_smul]
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp boolPhase.2
  · exact ⟨1, some 1, one_ne_zero, by
      simpa [boolPauliOption] using boolPhase_conj_X⟩
  · exact ⟨-1, some 0, neg_ne_zero.mpr one_ne_zero, by
      simpa [boolPauliOption] using boolPhase_conj_Y⟩
  · exact ⟨1, some 2, one_ne_zero, by
      simpa [boolPauliOption] using boolPhase_conj_Z⟩

theorem boolHadamardPhase_isBoolOneQubitPauliClifford :
    IsBoolOneQubitPauliClifford (boolHadamardPhase : Matrix Bool Bool ℂ) := by
  simpa [boolHadamardPhase] using
    isBoolOneQubitPauliClifford_mul boolHadamard boolPhase
      boolHadamard_isBoolOneQubitPauliClifford boolPhase_isBoolOneQubitPauliClifford

theorem boolTwoQubitCNOT_isBoolTwoQubitPauliClifford :
    IsBoolTwoQubitPauliClifford
      (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  intro p q
  refine ⟨boolTwoQubitCNOTScalar p q, (boolTwoQubitCNOTTarget p q).1,
    (boolTwoQubitCNOTTarget p q).2, ?_,
    boolTwoQubitCNOT_conj_boolTwoQubitPauli p q⟩
  fin_cases p <;> fin_cases q <;> simp +decide [boolTwoQubitCNOTScalar]

theorem boolTwoQubitSWAP_conj_boolTwoQubitPauli
    (p q : Option (Fin 3)) :
    (boolTwoQubitSWAP : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli p q *
        Matrix.conjTranspose (boolTwoQubitSWAP : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli q p := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [boolTwoQubitSWAP, boolTwoQubitSWAPMatrix, boolTwoQubitPauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker] <;>
    ring

theorem boolTwoQubitSWAP_isBoolTwoQubitPauliClifford :
    IsBoolTwoQubitPauliClifford
      (boolTwoQubitSWAP : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  intro p q
  exact ⟨1, q, p, one_ne_zero, by
    simpa using boolTwoQubitSWAP_conj_boolTwoQubitPauli p q⟩

theorem one_isBoolTwoQubitPauliClifford :
    IsBoolTwoQubitPauliClifford (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  intro p q
  exact ⟨1, p, q, one_ne_zero, by simp⟩

theorem isBoolTwoQubitPauliClifford_mul
    (U V : Matrix.unitaryGroup (Bool × Bool) ℂ)
    (hU : IsBoolTwoQubitPauliClifford (U : Matrix (Bool × Bool) (Bool × Bool) ℂ))
    (hV : IsBoolTwoQubitPauliClifford (V : Matrix (Bool × Bool) (Bool × Bool) ℂ)) :
    IsBoolTwoQubitPauliClifford
      ((U * V : Matrix.unitaryGroup (Bool × Bool) ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  intro p q
  obtain ⟨cV, r, s, hcV, hVpq⟩ := hV p q
  obtain ⟨cU, t, u, hcU, hUrs⟩ := hU r s
  refine ⟨cV * cU, t, u, mul_ne_zero hcV hcU, ?_⟩
  rw [unitary_mul_conjugation_smul U V _ _ _ hVpq, hUrs, smul_smul]

theorem isBoolTwoQubitPauliClifford_tensor
    (U V : Matrix.unitaryGroup Bool ℂ)
    (hU : IsBoolOneQubitPauliClifford (U : Matrix Bool Bool ℂ))
    (hV : IsBoolOneQubitPauliClifford (V : Matrix Bool Bool ℂ)) :
    IsBoolTwoQubitPauliClifford
      (Quantum.tensorGate U V : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  intro p q
  obtain ⟨c, r, hc, hUp⟩ := hU p
  obtain ⟨d, s, hd, hVq⟩ := hV q
  refine ⟨c * d, r, s, mul_ne_zero hc hd, ?_⟩
  rw [boolTwoQubitPauli, twoQubitTensor_conjugation, hUp, hVq]
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp [boolTwoQubitPauli, Matrix.kronecker, smul_eq_mul, mul_assoc, mul_left_comm]

theorem boolAxisNormalizer_isBoolOneQubitPauliClifford (p : Option (Fin 3)) :
    IsBoolOneQubitPauliClifford (boolAxisNormalizer p : Matrix Bool Bool ℂ) := by
  fin_cases p
  · intro q
    exact ⟨1, q, one_ne_zero, by simp [boolAxisNormalizer]⟩
  · simpa [boolAxisNormalizer] using boolHadamard_isBoolOneQubitPauliClifford
  · simpa [boolAxisNormalizer] using boolHadamardPhase_isBoolOneQubitPauliClifford
  · intro q
    exact ⟨1, q, one_ne_zero, by simp [boolAxisNormalizer]⟩

theorem boolTwoQubitLocalNormalizer_isBoolTwoQubitPauliClifford
    (p q : Option (Fin 3)) :
    IsBoolTwoQubitPauliClifford
      (boolTwoQubitLocalNormalizer p q : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  exact isBoolTwoQubitPauliClifford_tensor (boolAxisNormalizer p) (boolAxisNormalizer q)
    (boolAxisNormalizer_isBoolOneQubitPauliClifford p)
    (boolAxisNormalizer_isBoolOneQubitPauliClifford q)

theorem boolTwoQubitTransport_isBoolTwoQubitPauliClifford
    (p q : Option (Fin 3)) :
    IsBoolTwoQubitPauliClifford
      (boolTwoQubitTransport p q : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  by_cases hp : p = none
  · rw [boolTwoQubitTransport, if_pos hp]
    exact boolTwoQubitLocalNormalizer_isBoolTwoQubitPauliClifford p q
  · by_cases hq : q = none
    · rw [boolTwoQubitTransport, if_neg hp, if_pos hq]
      exact isBoolTwoQubitPauliClifford_mul boolTwoQubitSWAP
        (boolTwoQubitLocalNormalizer p q) boolTwoQubitSWAP_isBoolTwoQubitPauliClifford
        (boolTwoQubitLocalNormalizer_isBoolTwoQubitPauliClifford p q)
    · rw [boolTwoQubitTransport, if_neg hp, if_neg hq]
      exact isBoolTwoQubitPauliClifford_mul boolTwoQubitCNOT
        (boolTwoQubitLocalNormalizer p q) boolTwoQubitCNOT_isBoolTwoQubitPauliClifford
        (boolTwoQubitLocalNormalizer_isBoolTwoQubitPauliClifford p q)

theorem scalarSpecialUnitaryRepresentative_isBoolTwoQubitPauliClifford
    (U : Matrix.unitaryGroup (Bool × Bool) ℂ)
    (hU : IsBoolTwoQubitPauliClifford (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) :
    IsBoolTwoQubitPauliClifford
      (scalarSpecialUnitaryRepresentative U : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  intro p q
  obtain ⟨c, r, s, hc, htransport⟩ := hU p q
  refine ⟨c, r, s, hc, ?_⟩
  rw [scalarSpecialUnitaryRepresentative_conjugation_eq]
  exact htransport

theorem boolTwoQubitTransportSpecial_isBoolTwoQubitPauliClifford
    (p q : Option (Fin 3)) :
    IsBoolTwoQubitPauliClifford
      (scalarSpecialUnitaryRepresentative (boolTwoQubitTransport p q) :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) :=
  scalarSpecialUnitaryRepresentative_isBoolTwoQubitPauliClifford _
    (boolTwoQubitTransport_isBoolTwoQubitPauliClifford p q)

end

end GaloisForLFunctions.HTGeometry
