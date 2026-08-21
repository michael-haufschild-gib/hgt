/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRanks
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Hasse detection for block-triangular matrices

A fixed block decomposition of a global matrix is preserved and reflected by every completed
scalar extension.  Equivalently, preservation of a specified global flag can be tested locally.
This concerns a fixed global flag; it does not assert descent of independently chosen local flags.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

/-- Block-triangularity with respect to a fixed index map is reflected by field scalar
extension. -/
theorem matrix_blockTriangular_iff_map {K : Type u} {L : Type v} {n : Type w} {ι : Type x}
    [Field K] [Field L] [Algebra K L] [LT ι] (M : Matrix n n K) (b : n → ι) :
    M.BlockTriangular b ↔ (M.map (algebraMap K L)).BlockTriangular b := by
  constructor
  · exact Matrix.BlockTriangular.map (algebraMap K L)
  · intro h i j hij
    apply FaithfulSMul.algebraMap_injective K L
    simpa only [Matrix.map_apply, map_zero] using h hij

/-- A number-field matrix preserves a fixed block flag exactly when every completed matrix
preserves that flag. -/
theorem numberFieldMatrix_blockTriangular_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    {ι : Type x} [LT ι] (M : Matrix n n K) (b : n → ι) :
    M.BlockTriangular b ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).BlockTriangular b := by
  constructor
  · intro h p
    exact (matrix_blockTriangular_iff_map (L := completion K p) M b).mp h
  · intro h
    exact (matrix_blockTriangular_iff_map (L := completion K (witnessPlace K)) M b).mpr
      (h (witnessPlace K))

/-- An `F(t)`-matrix preserves a fixed block flag exactly when every finite and infinite
completed matrix preserves that flag. -/
theorem rationalFunctionMatrix_blockTriangular_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    {ι : Type x} [LT ι] (M : Matrix n n (RatFunc F)) (b : n → ι) :
    M.BlockTriangular b ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).BlockTriangular b := by
  constructor
  · intro h p
    exact (matrix_blockTriangular_iff_map (L := rationalFunctionCompletion F p) M b).mp h
  · intro h
    exact (matrix_blockTriangular_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) M b).mpr
      (h RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
