import GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure
import Mathlib.Data.Real.Basic

/-!
# Joint source reversal is the unique idempotent-indecomposable fixed algebra

The two individual source reversals fix split real algebras containing nontrivial idempotents.
Their joint reversal fixes the generated complex scalar algebra, whose only idempotents are zero
and one. Thus, among the three order-two source reversals in the finite source-pair model, joint
reversal is uniquely selected by absence of a nontrivial fixed idempotent.

This is standard finite real algebra. It does not derive a physical no-spectator principle,
quantum theory, spacetime, gravity, gauge forces, or any prediction.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

variable {K : Type*} [Field K]

/-- Coordinate form of the split algebra fixed by record-source reversal. -/
def recordSplitScalar (a d : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a, 0; 0, d]

/-- Coordinate form of the split algebra fixed by paired-source reversal. -/
def pairSplitScalar (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  a • 1 + b • pairRecordMatrix

/-- Entrywise form of record-source reversal. -/
theorem recordSourceReversal_apply
    (A : Matrix (Fin 2) (Fin 2) K) :
    recordSourceReversal A =
      !![A 0 0, -A 0 1; -A 1 0, A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordSourceReversal, recordPolarityMatrix,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Entrywise form of paired-source reversal. -/
theorem pairSourceReversal_apply
    (A : Matrix (Fin 2) (Fin 2) K) :
    pairSourceReversal A =
      !![A 1 1, A 1 0; A 0 1, A 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairSourceReversal, pairRecordMatrix,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Record-source reversal fixes exactly the diagonal split algebra. -/
theorem recordSourceReversal_fixed_iff_splitScalar
    [CharZero K] (A : Matrix (Fin 2) (Fin 2) K) :
    recordSourceReversal A = A ↔
      ∃ a d : K, A = recordSplitScalar a d := by
  constructor
  · intro h
    rw [recordSourceReversal_apply] at h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
    have h10 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) h
    simp at h01 h10
    have hz01 : A 0 1 = 0 :=
      CharZero.eq_neg_self_iff.mp h01.symm
    have hz10 : A 1 0 = 0 :=
      CharZero.eq_neg_self_iff.mp h10.symm
    refine ⟨A 0 0, A 1 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [recordSplitScalar, hz01, hz10]
  · rintro ⟨a, d, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [recordSourceReversal_apply, recordSplitScalar]

/-- Paired-source reversal fixes exactly the symmetric split algebra. -/
theorem pairSourceReversal_fixed_iff_splitScalar
    (A : Matrix (Fin 2) (Fin 2) K) :
    pairSourceReversal A = A ↔
      ∃ a b : K, A = pairSplitScalar a b := by
  constructor
  · intro h
    rw [pairSourceReversal_apply] at h
    have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
    simp at h00 h01
    refine ⟨A 0 0, A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [pairSplitScalar, pairRecordMatrix]
    · simp [pairSplitScalar, pairRecordMatrix]
    · simpa [pairSplitScalar, pairRecordMatrix] using h01
    · simpa [pairSplitScalar, pairRecordMatrix] using h00
  · rintro ⟨a, b, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairSourceReversal_apply, pairSplitScalar, pairRecordMatrix]

/-- A nontrivial idempotent in the record-reversal fixed algebra. -/
def recordFixedSector : Matrix (Fin 2) (Fin 2) ℝ :=
  recordSplitScalar 1 0

/-- A nontrivial idempotent in the paired-reversal fixed algebra. -/
def pairFixedSector : Matrix (Fin 2) (Fin 2) ℝ :=
  pairSplitScalar (1 / 2) (1 / 2)

theorem recordFixedSector_fixed :
    recordSourceReversal recordFixedSector = recordFixedSector := by
  exact (recordSourceReversal_fixed_iff_splitScalar recordFixedSector).2
    ⟨1, 0, rfl⟩

theorem pairFixedSector_fixed :
    pairSourceReversal pairFixedSector = pairFixedSector := by
  exact (pairSourceReversal_fixed_iff_splitScalar pairFixedSector).2
    ⟨1 / 2, 1 / 2, rfl⟩

theorem recordFixedSector_idempotent :
    recordFixedSector * recordFixedSector = recordFixedSector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordFixedSector, recordSplitScalar, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem pairFixedSector_idempotent :
    pairFixedSector * pairFixedSector = pairFixedSector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairFixedSector, pairSplitScalar, pairRecordMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem recordFixedSector_ne_zero : recordFixedSector ≠ 0 := by
  intro h
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  simp [recordFixedSector, recordSplitScalar] at h00

theorem recordFixedSector_ne_one : recordFixedSector ≠ 1 := by
  intro h
  have h11 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
  simp [recordFixedSector, recordSplitScalar] at h11

theorem pairFixedSector_ne_zero : pairFixedSector ≠ 0 := by
  intro h
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  simp [pairFixedSector, pairSplitScalar, pairRecordMatrix] at h00

theorem pairFixedSector_ne_one : pairFixedSector ≠ 1 := by
  intro h
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  simp [pairFixedSector, pairSplitScalar, pairRecordMatrix] at h00

/-- Every idempotent fixed by joint source reversal is zero or one. -/
theorem sourcePairParity_fixed_idempotent_eq_zero_or_one
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hfixed : sourcePairParity A = A)
    (hidempotent : A * A = A) :
    A = 0 ∨ A = 1 := by
  obtain ⟨a, b, rfl⟩ :=
    (sourcePairParity_fixed_iff_complexScalar A).mp hfixed
  rw [sourceComplexScalar_mul] at hidempotent
  have hp :
      (a * a - b * b, a * b + b * a) = (a, b) :=
    sourceComplexScalar_pair_injective hidempotent
  have ha : a * a - b * b = a := congrArg Prod.fst hp
  have hb : a * b + b * a = b := congrArg Prod.snd hp
  by_cases hb0 : b = 0
  · subst b
    have ha01 : a = 0 ∨ a = 1 := by
      rcases eq_zero_or_eq_zero_of_mul_eq_zero
          (show a * (a - 1) = 0 by nlinarith) with ha0 | ha1
      · exact Or.inl ha0
      · exact Or.inr (sub_eq_zero.mp ha1)
    rcases ha01 with rfl | rfl
    · left
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sourceComplexScalar, sourceOrderedPairComplexStructure,
          recordPolarityMatrix, pairRecordMatrix]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sourceComplexScalar, sourceOrderedPairComplexStructure,
          recordPolarityMatrix, pairRecordMatrix]
  · have hprod : b * (2 * a - 1) = 0 := by
      nlinarith [hb]
    have htwoa : 2 * a = 1 := by
      rcases mul_eq_zero.mp hprod with hbzero | hfactor
      · exact False.elim (hb0 hbzero)
      · nlinarith [hfactor]
    have hsq : 0 ≤ b ^ 2 := sq_nonneg b
    exfalso
    nlinarith [ha, htwoa, hsq]

/-- **No-spectator source selector.** Joint source reversal is the only one of the three
source-pair reversals whose real fixed algebra has no nontrivial idempotent. -/
theorem jointSourceReversal_only_idempotentIndecomposable :
    (∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      sourcePairParity A = A → A * A = A → A = 0 ∨ A = 1) ∧
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      recordSourceReversal A = A ∧ A * A = A ∧ A ≠ 0 ∧ A ≠ 1) ∧
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      pairSourceReversal A = A ∧ A * A = A ∧ A ≠ 0 ∧ A ≠ 1) := by
  exact ⟨sourcePairParity_fixed_idempotent_eq_zero_or_one,
    ⟨recordFixedSector, recordFixedSector_fixed,
      recordFixedSector_idempotent, recordFixedSector_ne_zero,
      recordFixedSector_ne_one⟩,
    ⟨pairFixedSector, pairFixedSector_fixed,
      pairFixedSector_idempotent, pairFixedSector_ne_zero,
      pairFixedSector_ne_one⟩⟩

end GaloisForLFunctions.HTGeometry
