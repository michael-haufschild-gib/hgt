/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixSingularity

/-!
# Hasse detection for invertible matrices

For square matrices over global fields, the determinant Hasse test upgrades to a test for being a
unit in the matrix ring.  Thus a globally specified matrix has an inverse exactly when each of
its completed scalar extensions has an inverse.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-- A square matrix over a number field is invertible exactly when all its completed scalar
extensions are invertible. -/
theorem numberFieldMatrix_isUnit_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    IsUnit M ↔ ∀ v : NumberFieldPlace K, IsUnit (M.map (placeEmbedding K v)) := by
  constructor
  · intro h v
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact (numberFieldMatrix_det_ne_zero_iff_forall_place K n M).mp
      (by rwa [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]) v
  · intro h
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    apply (numberFieldMatrix_det_ne_zero_iff_forall_place K n M).mpr
    intro v
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (h v)).ne_zero

/-- A square matrix over `F(t)` is invertible exactly when all its finite and infinite completed
scalar extensions are invertible. -/
theorem rationalFunctionMatrix_isUnit_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    IsUnit M ↔ ∀ v : RationalFunctionPlace F,
      IsUnit (M.map (rationalFunctionPlaceEmbedding F v)) := by
  constructor
  · intro h v
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact (rationalFunctionMatrix_det_ne_zero_iff_forall_place F n M).mp
      (by rwa [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]) v
  · intro h
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    apply (rationalFunctionMatrix_det_ne_zero_iff_forall_place F n M).mpr
    intro v
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (h v)).ne_zero

/-- Invertibility of a number-field matrix is detected at one completion. -/
theorem numberFieldMatrix_isUnit_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    IsUnit M ↔ ∃ v : NumberFieldPlace K, IsUnit (M.map (placeEmbedding K v)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldMatrix_isUnit_iff_forall_place K n M).mp h (witnessPlace K)⟩
  · rintro ⟨v, hv⟩
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact (numberFieldMatrix_det_ne_zero_iff_exists_place K n M).mpr
      ⟨v, ((Matrix.isUnit_iff_isUnit_det _).mp hv).ne_zero⟩

/-- Invertibility of a rational-function-field matrix is detected at one finite or infinite
completion. -/
theorem rationalFunctionMatrix_isUnit_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    IsUnit M ↔ ∃ v : RationalFunctionPlace F,
      IsUnit (M.map (rationalFunctionPlaceEmbedding F v)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionMatrix_isUnit_iff_forall_place F n M).mp h .infinite⟩
  · rintro ⟨v, hv⟩
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact (rationalFunctionMatrix_det_ne_zero_iff_exists_place F n M).mpr
      ⟨v, ((Matrix.isUnit_iff_isUnit_det _).mp hv).ne_zero⟩

end GaloisForLFunctions.HTGeometry.ABHN
