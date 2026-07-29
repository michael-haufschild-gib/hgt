import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Primitive records do not select their quadratic successor law

A one-step pointed record coalgebra has carrier `K·1 ⊕ P ⊕ K·z`. Its reduced coproduct vanishes
on the primitive plane `P` and sends the top coefficient `c` to `c • q`, where `q` is the first
higher-record tensor. Thus a nonzero `q` gives exactly the same primitive layer for every choice
of its projective congruence orbit.

This file certifies the smallest nonselection pair. On a two-dimensional primitive plane, the
paired tensor `[[0,1],[1,0]]` and the self tensor `[[0,0],[0,1]]` are both nonzero and symmetric.
Both therefore have exactly zero as primitive top coefficient, but they cannot be related by an
invertible change of primitive basis and nonzero rescaling: determinant nonvanishing distinguishes
their projective congruence orbits.

These are unconditional finite linear-algebra theorems. The file does not claim that a physical
event supplies either tensor, that every record coalgebra has this one-step form, or that a
successor operational law, gravity, spacetime, or a gauge force has been reconstructed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

variable {K : Type*} [Field K]

/-- Reduced coproduct carried by the top coefficient of a one-step record. The omitted primitive
plane has identically zero reduced coproduct. -/
def reducedRecordCoproduct
    (q : Matrix (Fin 2) (Fin 2) K) (topCoefficient : K) :
    Matrix (Fin 2) (Fin 2) K :=
  topCoefficient • q

/-- For a nonzero higher-record tensor, the only primitive top coefficient is zero. Hence the
primitive part of the corresponding one-step record is precisely its prescribed primitive
plane. -/
theorem reducedRecordCoproduct_eq_zero_iff
    {q : Matrix (Fin 2) (Fin 2) K} (hq : q ≠ 0) (topCoefficient : K) :
    reducedRecordCoproduct q topCoefficient = 0 ↔ topCoefficient = 0 := by
  simp [reducedRecordCoproduct, hq]

/-- Projective congruence relation governing changes of primitive basis and rescaling of the
one-dimensional top record layer. -/
def ProjectivelyCongruent
    (q q' : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ (g : Matrix (Fin 2) (Fin 2) K) (a : K),
    g.det ≠ 0 ∧ a ≠ 0 ∧ gᵀ * q * g = a • q'

/-- Projective congruence preserves nonvanishing determinant, the rank-two orbit invariant in the
two-dimensional case. -/
theorem det_ne_zero_of_projectivelyCongruent
    {q q' : Matrix (Fin 2) (Fin 2) K}
    (h : ProjectivelyCongruent q q') (hq : q.det ≠ 0) :
    q'.det ≠ 0 := by
  rcases h with ⟨g, a, hg, ha, heq⟩
  intro hq'
  have hleft : (gᵀ * q * g).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hg hq) hg
  apply hleft
  rw [heq, Matrix.det_smul, hq', mul_zero]

/-- Rank-two paired-composition tensor. -/
def pairRecordMatrix : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

/-- Rank-one self-composition tensor. -/
def selfRecordMatrix : Matrix (Fin 2) (Fin 2) K :=
  !![0, 0; 0, 1]

@[simp]
theorem pairRecordMatrix_det :
    (pairRecordMatrix : Matrix (Fin 2) (Fin 2) K).det = -1 := by
  simp [pairRecordMatrix, Matrix.det_fin_two]

@[simp]
theorem selfRecordMatrix_det :
    (selfRecordMatrix : Matrix (Fin 2) (Fin 2) K).det = 0 := by
  simp [selfRecordMatrix, Matrix.det_fin_two]

@[simp]
theorem pairRecordMatrix_transpose :
    (pairRecordMatrix : Matrix (Fin 2) (Fin 2) K)ᵀ = pairRecordMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairRecordMatrix]

@[simp]
theorem selfRecordMatrix_transpose :
    (selfRecordMatrix : Matrix (Fin 2) (Fin 2) K)ᵀ = selfRecordMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [selfRecordMatrix]

theorem pairRecordMatrix_ne_zero :
    (pairRecordMatrix : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
  intro h
  have hentry := congrArg (fun q : Matrix (Fin 2) (Fin 2) K => q 0 1) h
  simp [pairRecordMatrix] at hentry

theorem selfRecordMatrix_ne_zero :
    (selfRecordMatrix : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
  intro h
  have hentry := congrArg (fun q : Matrix (Fin 2) (Fin 2) K => q 1 1) h
  simp [selfRecordMatrix] at hentry

/-- The paired and self tensors define inequivalent first higher-record laws despite living on the
same primitive plane. -/
theorem pairRecord_not_projectivelyCongruent_selfRecord :
    ¬ ProjectivelyCongruent
      (pairRecordMatrix : Matrix (Fin 2) (Fin 2) K)
      selfRecordMatrix := by
  intro h
  have hself : (selfRecordMatrix : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    det_ne_zero_of_projectivelyCongruent h (by simp)
  exact hself (by simp)

/-- Both explicit record laws have exactly zero as primitive top coefficient. -/
theorem pair_self_primitive_top_coefficients
    (topCoefficient : K) :
    (reducedRecordCoproduct pairRecordMatrix topCoefficient = 0 ↔
      topCoefficient = 0) ∧
    (reducedRecordCoproduct selfRecordMatrix topCoefficient = 0 ↔
      topCoefficient = 0) :=
  ⟨reducedRecordCoproduct_eq_zero_iff pairRecordMatrix_ne_zero topCoefficient,
    reducedRecordCoproduct_eq_zero_iff selfRecordMatrix_ne_zero topCoefficient⟩

/-- **Primitive-record quadratic nonselection law.** Two symmetric nonzero quadratic record
tensors have the same primitive top-coefficient criterion but belong to different projective
congruence orbits. Primitive obstruction data alone therefore do not select the first
higher-record composition law. -/
theorem primitiveRecordQuadraticNonselection :
    (∀ topCoefficient : K,
      (reducedRecordCoproduct pairRecordMatrix topCoefficient = 0 ↔
        topCoefficient = 0) ∧
      (reducedRecordCoproduct selfRecordMatrix topCoefficient = 0 ↔
        topCoefficient = 0)) ∧
    ¬ ProjectivelyCongruent
      (pairRecordMatrix : Matrix (Fin 2) (Fin 2) K)
      selfRecordMatrix :=
  ⟨pair_self_primitive_top_coefficients,
    pairRecord_not_projectivelyCongruent_selfRecord⟩

end GaloisForLFunctions.HTGeometry
