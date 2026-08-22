/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixAdjoints
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Hasse detection for diagonal and orthogonal matrix systems

Diagonal form, and pairwise orthogonality of rows or columns, are reflected by field scalar
extension. These provide completion-wise tests relative to a fixed global basis; they do not
assert that independently chosen local diagonalizing bases glue globally.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

/-- Diagonality of a fixed square matrix is reflected by coefficientwise field scalar extension.
-/
theorem matrix_isDiag_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] (M : Matrix n n K) :
    M.IsDiag ↔ (M.map (algebraMap K L)).IsDiag := by
  constructor
  · intro h
    exact h.map (map_zero _)
  · intro h i j hij
    apply FaithfulSMul.algebraMap_injective K L
    simpa only [Matrix.map_apply, map_zero] using h hij

/-- Pairwise orthogonality of the rows of a matrix is reflected by coefficientwise field scalar
extension. -/
theorem matrix_hasOrthogonalRows_iff_map {K : Type u} {L : Type v} {m : Type w} {n : Type x}
    [Field K] [Field L] [Algebra K L] [Fintype n] (M : Matrix m n K) :
    M.HasOrthogonalRows ↔ (M.map (algebraMap K L)).HasOrthogonalRows := by
  rw [← Matrix.mul_transpose_self_isDiag_iff_hasOrthogonalRows,
    ← Matrix.mul_transpose_self_isDiag_iff_hasOrthogonalRows, ← Matrix.transpose_map,
    ← Matrix.map_mul]
  exact matrix_isDiag_iff_map _

/-- Pairwise orthogonality of the columns of a matrix is reflected by coefficientwise field scalar
extension. -/
theorem matrix_hasOrthogonalCols_iff_map {K : Type u} {L : Type v} {m : Type w} {n : Type x}
    [Field K] [Field L] [Algebra K L] [Fintype m] (M : Matrix m n K) :
    M.HasOrthogonalCols ↔ (M.map (algebraMap K L)).HasOrthogonalCols := by
  rw [← Matrix.transpose_mul_self_isDiag_iff_hasOrthogonalCols,
    ← Matrix.transpose_mul_self_isDiag_iff_hasOrthogonalCols, ← Matrix.transpose_map,
    ← Matrix.map_mul]
  exact matrix_isDiag_iff_map _

/-- A number-field matrix is diagonal exactly when every completed matrix is diagonal. -/
theorem numberFieldMatrix_isDiag_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) (M : Matrix n n K) :
    M.IsDiag ↔ ∀ p : NumberFieldPlace K, (M.map (algebraMap K (completion K p))).IsDiag := by
  constructor
  · intro h p
    exact (matrix_isDiag_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_isDiag_iff_map (L := completion K (witnessPlace K)) M).mpr
      (h (witnessPlace K))

/-- An `F(t)`-matrix is diagonal exactly when every finite and infinite completed matrix is. -/
theorem rationalFunctionMatrix_isDiag_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) (M : Matrix n n (RatFunc F)) :
    M.IsDiag ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).IsDiag := by
  constructor
  · intro h p
    exact (matrix_isDiag_iff_map (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_isDiag_iff_map
      (L := rationalFunctionCompletion F .infinite) M).mpr (h .infinite)

/-- A number-field matrix has pairwise orthogonal rows exactly when every completed matrix does.
-/
theorem numberFieldMatrix_hasOrthogonalRows_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {m : Type w} {n : Type x} [Fintype n]
    (M : Matrix m n K) :
    M.HasOrthogonalRows ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).HasOrthogonalRows := by
  constructor
  · intro h p
    exact (matrix_hasOrthogonalRows_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_hasOrthogonalRows_iff_map (L := completion K (witnessPlace K)) M).mpr
      (h (witnessPlace K))

/-- An `F(t)`-matrix has pairwise orthogonal rows exactly when every finite and infinite completed
matrix does. -/
theorem rationalFunctionMatrix_hasOrthogonalRows_iff_forall_place
    (F : Type u) [Field F] [Finite F] {m : Type w} {n : Type x} [Fintype n]
    (M : Matrix m n (RatFunc F)) :
    M.HasOrthogonalRows ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).HasOrthogonalRows := by
  constructor
  · intro h p
    exact (matrix_hasOrthogonalRows_iff_map (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_hasOrthogonalRows_iff_map
      (L := rationalFunctionCompletion F .infinite) M).mpr (h .infinite)

/-- A number-field matrix has pairwise orthogonal columns exactly when every completed matrix
does. -/
theorem numberFieldMatrix_hasOrthogonalCols_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {m : Type w} {n : Type x} [Fintype m]
    (M : Matrix m n K) :
    M.HasOrthogonalCols ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).HasOrthogonalCols := by
  constructor
  · intro h p
    exact (matrix_hasOrthogonalCols_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_hasOrthogonalCols_iff_map (L := completion K (witnessPlace K)) M).mpr
      (h (witnessPlace K))

/-- An `F(t)`-matrix has pairwise orthogonal columns exactly when every finite and infinite
completed matrix does. -/
theorem rationalFunctionMatrix_hasOrthogonalCols_iff_forall_place
    (F : Type u) [Field F] [Finite F] {m : Type w} {n : Type x} [Fintype m]
    (M : Matrix m n (RatFunc F)) :
    M.HasOrthogonalCols ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).HasOrthogonalCols := by
  constructor
  · intro h p
    exact (matrix_hasOrthogonalCols_iff_map (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_hasOrthogonalCols_iff_map
      (L := rationalFunctionCompletion F .infinite) M).mpr (h .infinite)

/-- Diagonality of a number-field matrix can be certified at one completion. -/
theorem numberFieldMatrix_isDiag_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) (M : Matrix n n K) :
    M.IsDiag ↔ ∃ p : NumberFieldPlace K, (M.map (algebraMap K (completion K p))).IsDiag := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (matrix_isDiag_iff_map (L := completion K (witnessPlace K)) M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_isDiag_iff_map (L := completion K p) M).mpr hp

/-- Diagonality of an `F(t)`-matrix can be certified at one completion. -/
theorem rationalFunctionMatrix_isDiag_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) (M : Matrix n n (RatFunc F)) :
    M.IsDiag ↔ ∃ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).IsDiag := by
  constructor
  · intro h
    exact ⟨.infinite,
      (matrix_isDiag_iff_map (L := rationalFunctionCompletion F .infinite) M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_isDiag_iff_map (L := rationalFunctionCompletion F p) M).mpr hp

/-- Orthogonality of rows of a number-field matrix can be certified at one completion. -/
theorem numberFieldMatrix_hasOrthogonalRows_iff_exists_place
    (K : Type u) [Field K] [NumberField K] {m : Type w} {n : Type x} [Fintype n]
    (M : Matrix m n K) :
    M.HasOrthogonalRows ↔ ∃ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).HasOrthogonalRows := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (matrix_hasOrthogonalRows_iff_map (L := completion K (witnessPlace K)) M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_hasOrthogonalRows_iff_map (L := completion K p) M).mpr hp

/-- Orthogonality of rows of an `F(t)`-matrix can be certified at one completion. -/
theorem rationalFunctionMatrix_hasOrthogonalRows_iff_exists_place
    (F : Type u) [Field F] [Finite F] {m : Type w} {n : Type x} [Fintype n]
    (M : Matrix m n (RatFunc F)) :
    M.HasOrthogonalRows ↔ ∃ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).HasOrthogonalRows := by
  constructor
  · intro h
    exact ⟨.infinite,
      (matrix_hasOrthogonalRows_iff_map (L := rationalFunctionCompletion F .infinite) M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_hasOrthogonalRows_iff_map (L := rationalFunctionCompletion F p) M).mpr hp

/-- Orthogonality of columns of a number-field matrix can be certified at one completion. -/
theorem numberFieldMatrix_hasOrthogonalCols_iff_exists_place
    (K : Type u) [Field K] [NumberField K] {m : Type w} {n : Type x} [Fintype m]
    (M : Matrix m n K) :
    M.HasOrthogonalCols ↔ ∃ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).HasOrthogonalCols := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (matrix_hasOrthogonalCols_iff_map (L := completion K (witnessPlace K)) M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_hasOrthogonalCols_iff_map (L := completion K p) M).mpr hp

/-- Orthogonality of columns of an `F(t)`-matrix can be certified at one completion. -/
theorem rationalFunctionMatrix_hasOrthogonalCols_iff_exists_place
    (F : Type u) [Field F] [Finite F] {m : Type w} {n : Type x} [Fintype m]
    (M : Matrix m n (RatFunc F)) :
    M.HasOrthogonalCols ↔ ∃ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).HasOrthogonalCols := by
  constructor
  · intro h
    exact ⟨.infinite,
      (matrix_hasOrthogonalCols_iff_map (L := rationalFunctionCompletion F .infinite) M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_hasOrthogonalCols_iff_map (L := rationalFunctionCompletion F p) M).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
