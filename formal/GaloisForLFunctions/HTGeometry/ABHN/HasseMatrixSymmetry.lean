/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixAdjoints
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Hasse detection for symmetric matrices

Symmetry of a fixed matrix is reflected by field scalar extension. This gives an all-place test
for symmetric coefficient matrices without requiring a finite index type.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- Symmetry of a matrix is reflected by coefficientwise field scalar extension. -/
theorem matrix_isSymm_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] (M : Matrix n n K) :
    M.IsSymm ↔ (M.map (algebraMap K L)).IsSymm := by
  exact (Matrix.isSymm_map_iff (FaithfulSMul.algebraMap_injective K L)).symm

/-- A number-field matrix is symmetric exactly when every completed matrix is symmetric. -/
theorem numberFieldMatrix_isSymm_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) (M : Matrix n n K) :
    M.IsSymm ↔ ∀ p : NumberFieldPlace K, (M.map (algebraMap K (completion K p))).IsSymm := by
  constructor
  · intro h p
    exact (matrix_isSymm_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_isSymm_iff_map (L := completion K (witnessPlace K)) M).mpr
      (h (witnessPlace K))

/-- An `F(t)`-matrix is symmetric exactly when every finite and infinite completed matrix is. -/
theorem rationalFunctionMatrix_isSymm_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) (M : Matrix n n (RatFunc F)) :
    M.IsSymm ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).IsSymm := by
  constructor
  · intro h p
    exact (matrix_isSymm_iff_map (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_isSymm_iff_map
      (L := rationalFunctionCompletion F .infinite) M).mpr (h .infinite)

/-- Symmetry of a number-field matrix can be certified at one completion. -/
theorem numberFieldMatrix_isSymm_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) (M : Matrix n n K) :
    M.IsSymm ↔ ∃ p : NumberFieldPlace K, (M.map (algebraMap K (completion K p))).IsSymm := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (matrix_isSymm_iff_map (L := completion K (witnessPlace K)) M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_isSymm_iff_map (L := completion K p) M).mpr hp

/-- Symmetry of an `F(t)`-matrix can be certified at one completion. -/
theorem rationalFunctionMatrix_isSymm_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) (M : Matrix n n (RatFunc F)) :
    M.IsSymm ↔ ∃ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).IsSymm := by
  constructor
  · intro h
    exact ⟨.infinite,
      (matrix_isSymm_iff_map (L := rationalFunctionCompletion F .infinite) M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_isSymm_iff_map (L := rationalFunctionCompletion F p) M).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
