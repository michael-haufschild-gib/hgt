import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import GaloisForLFunctions.HTGeometry.HaferkampSpecialUnitaryPhase

/-!
# First explicit two-qubit Clifford seed for the Haferkamp et al. transport

Appendix B of Haferkamp--Faist--Kothakonda--Eisert--Yunger Halpern (2022)
uses two-qubit Clifford gates to merge Pauli support along a backward-light
cone.  This module installs the Boolean-basis CNOT seed as a literal `SU(4)`
matrix and proves its first Pauli transport rule.  Later modules build the
complete local transport classification from these exact identities.
-/

open Matrix
open scoped Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- CNOT in the Boolean computational basis, with the first qubit as control
and the second as target. -/
def boolTwoQubitCNOTMatrix : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun row column =>
    if row.1 = column.1 ∧ row.2 = Bool.xor column.1 column.2 then 1 else 0

/-- The Boolean-basis CNOT matrix is unitary. -/
theorem boolTwoQubitCNOTMatrix_mem_unitary :
    boolTwoQubitCNOTMatrix ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [boolTwoQubitCNOTMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply, Bool.xor]

/-- CNOT as a bundled two-qubit unitary. -/
def boolTwoQubitCNOT : Matrix.unitaryGroup (Bool × Bool) ℂ :=
  ⟨boolTwoQubitCNOTMatrix, boolTwoQubitCNOTMatrix_mem_unitary⟩

/-- Tensor-product two-qubit Pauli matrix in the Boolean computational basis. -/
def boolTwoQubitPauli (p q : Option (Fin 3)) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.kronecker (boolPauliOption p) (boolPauliOption q)

/-- CNOT transports a target `Z` to the two-site `Z ⊗ Z` Pauli string. -/
theorem boolTwoQubitCNOT_conj_targetZ :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli none (some 2) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 2) (some 2) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.kronecker, Bool.xor]

/-- CNOT merges the two-site `Z ⊗ Z` Pauli string into target `Z`. -/
theorem boolTwoQubitCNOT_conj_twoZ :
    (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 2) (some 2) *
        Matrix.conjTranspose (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli none (some 2) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      boolTwoQubitCNOT, boolTwoQubitCNOTMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.kronecker, Bool.xor]

/-- The CNOT seed represented as an element of the paper's `SU(4)` gate
parameter space. -/
noncomputable def boolTwoQubitCNOTSpecial :
    Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  scalarSpecialUnitaryRepresentative boolTwoQubitCNOT

/-- The determinant-one CNOT representative obeys the same exact target-
`Z` transport rule. -/
theorem boolTwoQubitCNOTSpecial_conj_targetZ :
    (boolTwoQubitCNOTSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli none (some 2) *
        Matrix.conjTranspose
          (boolTwoQubitCNOTSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli (some 2) (some 2) := by
  rw [show (boolTwoQubitCNOTSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      scalarSpecialUnitaryPhase boolTwoQubitCNOT •
        (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) from rfl]
  exact (scalar_smul_conjugation_eq _ _ _
    (scalarSpecialUnitaryPhase_unitary boolTwoQubitCNOT)).trans
      boolTwoQubitCNOT_conj_targetZ

/-- The determinant-one CNOT representative also merges `Z ⊗ Z` to target
`Z`. -/
theorem boolTwoQubitCNOTSpecial_conj_twoZ :
    (boolTwoQubitCNOTSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 2) (some 2) *
        Matrix.conjTranspose
          (boolTwoQubitCNOTSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli none (some 2) := by
  rw [show (boolTwoQubitCNOTSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      scalarSpecialUnitaryPhase boolTwoQubitCNOT •
        (boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) from rfl]
  exact (scalar_smul_conjugation_eq _ _ _
    (scalarSpecialUnitaryPhase_unitary boolTwoQubitCNOT)).trans
      boolTwoQubitCNOT_conj_twoZ

/-- SWAP in the Boolean computational basis. -/
def boolTwoQubitSWAPMatrix : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun row column =>
    if row.1 = column.2 ∧ row.2 = column.1 then 1 else 0

/-- The Boolean-basis SWAP matrix is unitary. -/
theorem boolTwoQubitSWAPMatrix_mem_unitary :
    boolTwoQubitSWAPMatrix ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [boolTwoQubitSWAPMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply]

/-- SWAP as a bundled two-qubit unitary. -/
def boolTwoQubitSWAP : Matrix.unitaryGroup (Bool × Bool) ℂ :=
  ⟨boolTwoQubitSWAPMatrix, boolTwoQubitSWAPMatrix_mem_unitary⟩

/-- SWAP moves source `Z` to target `Z`. -/
theorem boolTwoQubitSWAP_conj_sourceZ :
    (boolTwoQubitSWAP : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 2) none *
        Matrix.conjTranspose (boolTwoQubitSWAP : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli none (some 2) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp +decide [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      boolTwoQubitSWAP, boolTwoQubitSWAPMatrix, boolTwoQubitPauli,
      boolPauliOption, finiteQubitPauli, Matrix.kronecker]

/-- The SWAP seed represented in `SU(4)`. -/
noncomputable def boolTwoQubitSWAPSpecial :
    Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  scalarSpecialUnitaryRepresentative boolTwoQubitSWAP

/-- The determinant-one SWAP representative moves source `Z` to target `Z`. -/
theorem boolTwoQubitSWAPSpecial_conj_sourceZ :
    (boolTwoQubitSWAPSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli (some 2) none *
        Matrix.conjTranspose
          (boolTwoQubitSWAPSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitPauli none (some 2) := by
  rw [show (boolTwoQubitSWAPSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      scalarSpecialUnitaryPhase boolTwoQubitSWAP •
        (boolTwoQubitSWAP : Matrix (Bool × Bool) (Bool × Bool) ℂ) from rfl]
  exact (scalar_smul_conjugation_eq _ _ _
    (scalarSpecialUnitaryPhase_unitary boolTwoQubitSWAP)).trans
      boolTwoQubitSWAP_conj_sourceZ

/-- Hadamard in the Boolean computational basis. -/
def boolHadamardMatrix : Matrix Bool Bool ℂ :=
  fun row column =>
    if row = false then (1 / (Real.sqrt 2 : ℂ))
    else if column = false then (1 / (Real.sqrt 2 : ℂ))
    else -(1 / (Real.sqrt 2 : ℂ))

/-- The Boolean-basis Hadamard matrix is unitary. -/
theorem boolHadamardMatrix_mem_unitary :
    boolHadamardMatrix ∈ Matrix.unitaryGroup Bool ℂ := by
  have hsqrt : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boolHadamardMatrix, Matrix.mul_apply]
  all_goals
    field_simp
    rw [hsqrt]
    try ring

/-- Boolean-basis Hadamard as a bundled one-qubit unitary. -/
def boolHadamard : Matrix.unitaryGroup Bool ℂ :=
  ⟨boolHadamardMatrix, boolHadamardMatrix_mem_unitary⟩

/-- Hadamard sends the Pauli `X` direction exactly to `Z`. -/
theorem boolHadamard_conj_X :
    (boolHadamard : Matrix Bool Bool ℂ) * finiteQubitPauli 0 *
      Matrix.conjTranspose (boolHadamard : Matrix Bool Bool ℂ) = finiteQubitPauli 2 := by
  have hsqrt : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [boolHadamard, boolHadamardMatrix, finiteQubitPauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    field_simp <;> rw [hsqrt] <;> ring

/-- The single-qubit phase gate in the Boolean computational basis. -/
def boolPhaseMatrix : Matrix Bool Bool ℂ :=
  fun row column =>
    if row = column then if row = false then 1 else Complex.I else 0

/-- The Boolean-basis phase gate is unitary. -/
theorem boolPhaseMatrix_mem_unitary :
    boolPhaseMatrix ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boolPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Boolean-basis phase gate as a bundled unitary. -/
def boolPhase : Matrix.unitaryGroup Bool ℂ :=
  ⟨boolPhaseMatrix, boolPhaseMatrix_mem_unitary⟩

/-- The phase gate sends `Y` to `-X`. -/
theorem boolPhase_conj_Y :
    (boolPhase : Matrix Bool Bool ℂ) * finiteQubitPauli 1 *
      Matrix.conjTranspose (boolPhase : Matrix Bool Bool ℂ) = -finiteQubitPauli 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [boolPhase, boolPhaseMatrix, finiteQubitPauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Conjugation by a product of unitaries is the composition of the two
conjugations, with the right factor acting first. -/
theorem unitary_mul_conjugation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) :
    ((U * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) * M *
        Matrix.conjTranspose ((U * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) =
      (U : Matrix ι ι ℂ) *
        ((V : Matrix ι ι ℂ) * M * Matrix.conjTranspose (V : Matrix ι ι ℂ)) *
        Matrix.conjTranspose (U : Matrix ι ι ℂ) := by
  change (U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ) * M *
      Matrix.conjTranspose ((U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) = _
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- A one-qubit Clifford sending `Y` to `-Z`. -/
def boolHadamardPhase : Matrix.unitaryGroup Bool ℂ := boolHadamard * boolPhase

/-- Hadamard after phase normalization sends `Y` to `-Z`.  The harmless sign
is a nonzero scalar and is retained explicitly for the Pauli-span induction. -/
theorem boolHadamardPhase_conj_Y :
    (boolHadamardPhase : Matrix Bool Bool ℂ) * finiteQubitPauli 1 *
      Matrix.conjTranspose (boolHadamardPhase : Matrix Bool Bool ℂ) = -finiteQubitPauli 2 := by
  rw [boolHadamardPhase, unitary_mul_conjugation, boolPhase_conj_Y]
  simp only [Matrix.mul_neg, Matrix.neg_mul]
  rw [boolHadamard_conj_X]

end

end GaloisForLFunctions.HTGeometry
