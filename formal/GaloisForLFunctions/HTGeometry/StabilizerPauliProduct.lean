import GaloisForLFunctions.HTGeometry.PauliLabelDictionary
import GaloisForLFunctions.HTGeometry.LagrangianBasisFrequency
import GaloisForLFunctions.HTGeometry.PauliParseval
import GaloisForLFunctions.HTGeometry.PauliCharacterProjectorExtraction

/-!
# Products of a commuting family of Pauli matrices

A commuting family of labelled Pauli matrices multiplies over any subset to a sign times the Pauli
matrix of the subset sum of the labels.  The sign is a square root of one because the product of
commuting Hermitian involutions is again an involution.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- The Pauli matrix named by a binary symplectic label. -/
def pauliMat (u : PauliSymp n) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  finitePauliMatrix (pauliOf u)

theorem pauliMat_zero : pauliMat (0 : PauliSymp n) = 1 := by
  rw [pauliMat, pauliOf_zero]
  exact finitePauliMatrix_const_none

theorem pauliMat_mul_self (u : PauliSymp n) : pauliMat u * pauliMat u = 1 :=
  finitePauliMatrix_mul_self _

/-- The phase of the product of two labelled Pauli matrices. -/
def labPhase (u v : PauliSymp n) : ℂ := ∏ s, optPhase (pauliOf u s) (pauliOf v s)

theorem pauliMat_mul (u v : PauliSymp n) :
    pauliMat u * pauliMat v = labPhase u v • pauliMat (u + v) := by
  rw [pauliMat, pauliMat, pauliMat, finitePauliMatrix_mul, labPhase, optMul_pauliOf]

theorem commute_pauliMat {u v : PauliSymp n} (h : symForm u v = 0) :
    Commute (pauliMat u) (pauliMat v) := by
  have hconj0 := finitePauliMatrix_conj (pauliOf u) (pauliOf v)
  rw [finitePauliConjugationSign_pauliOf, h, signOf, if_pos rfl, one_smul] at hconj0
  have hconj : pauliMat u * pauliMat v * pauliMat u = pauliMat v := hconj0
  have hstep : pauliMat u * pauliMat v * pauliMat u * pauliMat u =
      pauliMat v * pauliMat u := by
    rw [hconj]
  rw [mul_assoc (pauliMat u * pauliMat v), pauliMat_mul_self, mul_one] at hstep
  exact hstep

theorem labPhase_sq {u v : PauliSymp n} (h : symForm u v = 0) :
    labPhase u v * labPhase u v = 1 := by
  have hc := commute_pauliMat h
  have hsq : (pauliMat u * pauliMat v) * (pauliMat u * pauliMat v) = 1 := by
    calc (pauliMat u * pauliMat v) * (pauliMat u * pauliMat v)
        = pauliMat u * (pauliMat v * pauliMat u) * pauliMat v := by
          simp only [mul_assoc]
      _ = pauliMat u * (pauliMat u * pauliMat v) * pauliMat v := by rw [hc.eq]
      _ = (pauliMat u * pauliMat u) * (pauliMat v * pauliMat v) := by
          simp only [mul_assoc]
      _ = 1 := by rw [pauliMat_mul_self, pauliMat_mul_self, mul_one]
  rw [pauliMat_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliMat_mul_self] at hsq
  have hentry := congrFun (congrFun hsq (fun _ => false)) (fun _ => false)
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hentry
  exact hentry

section Family

variable {b : Fin n → PauliSymp n}

/-- The subset sum of a labelled family. -/
def labSum (b : Fin n → PauliSymp n) (S : Finset (Fin n)) : PauliSymp n := ∑ i ∈ S, b i

theorem labSum_insert {a : Fin n} {S : Finset (Fin n)} (ha : a ∉ S) :
    labSum b (insert a S) = b a + labSum b S := by
  classical
  rw [labSum, labSum, Finset.sum_insert ha]

theorem symForm_labSum_right (u : PauliSymp n)
    (hu : ∀ i, symForm u (b i) = 0) (S : Finset (Fin n)) : symForm u (labSum b S) = 0 := by
  classical
  induction S using Finset.induction with
  | empty => rw [labSum, Finset.sum_empty, symForm_comm, symForm_zero_left]
  | insert a s ha ih =>
      rw [labSum, Finset.sum_insert ha, symForm_add_right, ← labSum, ih, hu a, add_zero]

theorem symForm_labSum (hb : ∀ i j, symForm (b i) (b j) = 0) (i : Fin n) (S : Finset (Fin n)) :
    symForm (b i) (labSum b S) = 0 :=
  symForm_labSum_right (b i) (fun j => hb i j) S

/-- The product of a commuting family of Pauli matrices over a subset. -/
def stabProd (b : Fin n → PauliSymp n) (hb : ∀ i j, symForm (b i) (b j) = 0)
    (S : Finset (Fin n)) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  S.noncommProd (fun i => pauliMat (b i)) fun i _ j _ _ => commute_pauliMat (hb i j)

theorem stabProd_empty (hb : ∀ i j, symForm (b i) (b j) = 0) : stabProd b hb ∅ = 1 :=
  Finset.noncommProd_empty _ _

theorem stabProd_insert (hb : ∀ i j, symForm (b i) (b j) = 0) {a : Fin n} {S : Finset (Fin n)}
    (ha : a ∉ S) : stabProd b hb (insert a S) = pauliMat (b a) * stabProd b hb S := by
  classical
  rw [stabProd, stabProd]
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ ha

/-- **The product over a subset is a square root of one times the subset-sum Pauli matrix.** -/
theorem exists_stabProd_smul (hb : ∀ i j, symForm (b i) (b j) = 0) (S : Finset (Fin n)) :
    ∃ c : ℂ, c * c = 1 ∧ stabProd b hb S = c • pauliMat (labSum b S) := by
  classical
  induction S using Finset.induction with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      rw [stabProd_empty, labSum, Finset.sum_empty, pauliMat_zero, one_smul]
  | insert a s ha ih =>
      obtain ⟨c, hc, hcs⟩ := ih
      refine ⟨c * labPhase (b a) (labSum b s), ?_, ?_⟩
      · have hph := labPhase_sq (symForm_labSum hb a s)
        calc c * labPhase (b a) (labSum b s) * (c * labPhase (b a) (labSum b s))
            = (c * c) * (labPhase (b a) (labSum b s) * labPhase (b a) (labSum b s)) := by ring
          _ = 1 := by rw [hc, hph, mul_one]
      · rw [stabProd_insert hb ha, hcs, Matrix.mul_smul, pauliMat_mul, smul_smul,
          labSum_insert ha]

theorem pauliCoeff_smul_pauliMat (c : ℂ) (u : PauliSymp n) :
    pauliCoeff (c • pauliMat u) (pauliOf u) = c := by
  classical
  have hbasis : pauliMat u = finitePauliMatrixBasis (Fin n) (pauliOf u) := by
    rw [finitePauliMatrixBasis_apply, pauliMat]
  rw [pauliCoeff, hbasis, map_smul, (finitePauliMatrixBasis (Fin n)).repr_self]
  simp

/-- The sign of the product over a subset. -/
def stabSign (b : Fin n → PauliSymp n) (hb : ∀ i j, symForm (b i) (b j) = 0)
    (S : Finset (Fin n)) : ℂ :=
  pauliCoeff (stabProd b hb S) (pauliOf (labSum b S))

theorem stabProd_eq_smul (hb : ∀ i j, symForm (b i) (b j) = 0) (S : Finset (Fin n)) :
    stabProd b hb S = stabSign b hb S • pauliMat (labSum b S) := by
  obtain ⟨c, _, hcs⟩ := exists_stabProd_smul hb S
  have hsign : stabSign b hb S = c := by
    rw [stabSign, hcs, pauliCoeff_smul_pauliMat]
  rw [hsign, hcs]

theorem stabSign_sq (hb : ∀ i j, symForm (b i) (b j) = 0) (S : Finset (Fin n)) :
    stabSign b hb S * stabSign b hb S = 1 := by
  obtain ⟨c, hc, hcs⟩ := exists_stabProd_smul hb S
  have hsign : stabSign b hb S = c := by
    rw [stabSign, hcs, pauliCoeff_smul_pauliMat]
  rw [hsign]
  exact hc

end Family

end GaloisForLFunctions.HTGeometry
