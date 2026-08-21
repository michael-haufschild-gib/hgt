/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixIsometries
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixInvariants
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Hasse detection for classical matrix groups

Membership in Mathlib's orthogonal, special-orthogonal, and symplectic matrix groups is
reflected by field scalar extension.  Consequently, for number fields and rational function
fields over finite fields, membership can be checked at every completion.

These are fixed-coordinate statements: they do not patch independently chosen local forms.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

attribute [local instance] starRingOfComm

/-- Orthogonal-group membership is reflected by coefficientwise field scalar extension. -/
theorem matrix_mem_orthogonalGroup_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M ∈ Matrix.orthogonalGroup n K ↔
      M.map (algebraMap K L) ∈ Matrix.orthogonalGroup n L := by
  rw [Matrix.mem_orthogonalGroup_iff', Matrix.mem_orthogonalGroup_iff']
  constructor
  · intro h
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h,
      Matrix.map_one (algebraMap K L) (map_zero _) (map_one _)]
  · intro h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (M.transpose * M).map (algebraMap K L) =
      (1 : Matrix n n K).map (algebraMap K L)
    rw [Matrix.map_mul, Matrix.transpose_map,
      Matrix.map_one (algebraMap K L) (map_zero _) (map_one _)]
    exact h

/-- Special-orthogonal-group membership is reflected by coefficientwise field scalar extension. -/
theorem matrix_mem_specialOrthogonalGroup_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M ∈ Matrix.specialOrthogonalGroup n K ↔
      M.map (algebraMap K L) ∈ Matrix.specialOrthogonalGroup n L := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rintro ⟨hOrthogonal, hDet⟩
    refine ⟨(matrix_mem_orthogonalGroup_iff_map (L := L) M).mp hOrthogonal, ?_⟩
    simpa using (matrix_det_eq_iff_map (L := L) M 1).mp hDet
  · rintro ⟨hOrthogonal, hDet⟩
    refine ⟨(matrix_mem_orthogonalGroup_iff_map (L := L) M).mpr hOrthogonal, ?_⟩
    exact (matrix_det_eq_iff_map (L := L) M 1).mpr (by simpa using hDet)

/-- Symplectic-group membership is reflected by coefficientwise field scalar extension. -/
theorem matrix_mem_symplecticGroup_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix (n ⊕ n) (n ⊕ n) K) :
    M ∈ Matrix.symplecticGroup n K ↔
      M.map (algebraMap K L) ∈ Matrix.symplecticGroup n L := by
  rw [SymplecticGroup.mem_iff, SymplecticGroup.mem_iff]
  constructor
  · intro h
    rw [← Matrix.transpose_map, ← Matrix.map_J n (algebraMap K L), ← Matrix.map_mul,
      ← Matrix.map_mul, h]
  · intro h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (M * Matrix.J n K * M.transpose).map (algebraMap K L) =
      (Matrix.J n K).map (algebraMap K L)
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_J]
    exact h

/-- A number-field matrix is orthogonal exactly when every completed matrix is orthogonal. -/
theorem numberFieldMatrix_mem_orthogonalGroup_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M ∈ Matrix.orthogonalGroup n K ↔ ∀ p : NumberFieldPlace K,
      M.map (algebraMap K (completion K p)) ∈ Matrix.orthogonalGroup n (completion K p) := by
  constructor
  · intro h p
    exact (matrix_mem_orthogonalGroup_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_mem_orthogonalGroup_iff_map (L := completion K (witnessPlace K)) M).mpr
      (h (witnessPlace K))

/-- An `F(t)`-matrix is orthogonal exactly when every finite and infinite completed matrix is. -/
theorem rationalFunctionMatrix_mem_orthogonalGroup_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    M ∈ Matrix.orthogonalGroup n (RatFunc F) ↔ ∀ p : RationalFunctionPlace F,
      M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) ∈
        Matrix.orthogonalGroup n (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact (matrix_mem_orthogonalGroup_iff_map (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_mem_orthogonalGroup_iff_map
      (L := rationalFunctionCompletion F .infinite) M).mpr (h .infinite)

/-- A number-field matrix is special orthogonal exactly when every completed matrix is. -/
theorem numberFieldMatrix_mem_specialOrthogonalGroup_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M ∈ Matrix.specialOrthogonalGroup n K ↔ ∀ p : NumberFieldPlace K,
      M.map (algebraMap K (completion K p)) ∈
        Matrix.specialOrthogonalGroup n (completion K p) := by
  constructor
  · intro h p
    exact (matrix_mem_specialOrthogonalGroup_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_mem_specialOrthogonalGroup_iff_map
      (L := completion K (witnessPlace K)) M).mpr (h (witnessPlace K))

/-- An `F(t)`-matrix is special orthogonal exactly when every completed matrix is. -/
theorem rationalFunctionMatrix_mem_specialOrthogonalGroup_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    M ∈ Matrix.specialOrthogonalGroup n (RatFunc F) ↔ ∀ p : RationalFunctionPlace F,
      M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) ∈
        Matrix.specialOrthogonalGroup n (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact (matrix_mem_specialOrthogonalGroup_iff_map
      (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_mem_specialOrthogonalGroup_iff_map
      (L := rationalFunctionCompletion F .infinite) M).mpr (h .infinite)

/-- A number-field matrix is symplectic exactly when every completed matrix is symplectic. -/
theorem numberFieldMatrix_mem_symplecticGroup_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix (n ⊕ n) (n ⊕ n) K) :
    M ∈ Matrix.symplecticGroup n K ↔ ∀ p : NumberFieldPlace K,
      M.map (algebraMap K (completion K p)) ∈ Matrix.symplecticGroup n (completion K p) := by
  constructor
  · intro h p
    exact (matrix_mem_symplecticGroup_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_mem_symplecticGroup_iff_map (L := completion K (witnessPlace K)) M).mpr
      (h (witnessPlace K))

/-- An `F(t)`-matrix is symplectic exactly when every finite and infinite completed matrix is. -/
theorem rationalFunctionMatrix_mem_symplecticGroup_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix (n ⊕ n) (n ⊕ n) (RatFunc F)) :
    M ∈ Matrix.symplecticGroup n (RatFunc F) ↔ ∀ p : RationalFunctionPlace F,
      M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) ∈
        Matrix.symplecticGroup n (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact (matrix_mem_symplecticGroup_iff_map (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_mem_symplecticGroup_iff_map
      (L := rationalFunctionCompletion F .infinite) M).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
