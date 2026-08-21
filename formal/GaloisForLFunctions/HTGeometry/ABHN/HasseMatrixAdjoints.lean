/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixIsometries
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Hasse detection for matrix adjoints

The relation that two matrices are adjoints relative to prescribed bilinear-form matrices is
reflected by field scalar extension. Consequently, adjoint pairs and self-adjoint operators with
fixed global forms can be checked at every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

/-- The prescribed adjoint-pair relation is reflected by coefficientwise field scalar extension.
-/
theorem matrix_isAdjointPair_iff_map {K : Type u} {L : Type v} {m : Type w} {n : Type x}
    [Field K] [Field L] [Algebra K L] [Fintype m] [Fintype n]
    (J : Matrix n n K) (J' : Matrix m m K) (A : Matrix m n K) (A' : Matrix n m K) :
    Matrix.IsAdjointPair J J' A A' ↔
      Matrix.IsAdjointPair (J.map (algebraMap K L)) (J'.map (algebraMap K L))
        (A.map (algebraMap K L)) (A'.map (algebraMap K L)) := by
  constructor
  · intro h
    change A.transpose * J' = J * A' at h
    change (A.map (algebraMap K L)).transpose * J'.map (algebraMap K L) =
      J.map (algebraMap K L) * A'.map (algebraMap K L)
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]
  · intro h
    change (A.map (algebraMap K L)).transpose * J'.map (algebraMap K L) =
      J.map (algebraMap K L) * A'.map (algebraMap K L) at h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (A.transpose * J').map (algebraMap K L) = (J * A').map (algebraMap K L)
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    exact h

/-- Self-adjointness with respect to a prescribed bilinear-form matrix is reflected by field
scalar extension. -/
theorem matrix_isSelfAdjoint_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n]
    (J A : Matrix n n K) :
    J.IsSelfAdjoint A ↔
      (J.map (algebraMap K L)).IsSelfAdjoint (A.map (algebraMap K L)) := by
  exact matrix_isAdjointPair_iff_map J J A A

/-- A pair of matrices over a number field is adjoint relative to fixed forms exactly when the
completed pairs are adjoint at every place. -/
theorem numberFieldMatrix_isAdjointPair_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {m : Type w} {n : Type x} [Fintype m] [Fintype n]
    (J : Matrix n n K) (J' : Matrix m m K) (A : Matrix m n K) (A' : Matrix n m K) :
    Matrix.IsAdjointPair J J' A A' ↔ ∀ p : NumberFieldPlace K,
      Matrix.IsAdjointPair (J.map (algebraMap K (completion K p)))
        (J'.map (algebraMap K (completion K p))) (A.map (algebraMap K (completion K p)))
        (A'.map (algebraMap K (completion K p))) := by
  constructor
  · intro h p
    exact (matrix_isAdjointPair_iff_map (L := completion K p) J J' A A').mp h
  · intro h
    exact (matrix_isAdjointPair_iff_map (L := completion K (witnessPlace K)) J J' A A').mpr
      (h (witnessPlace K))

/-- A pair of matrices over `F(t)` is adjoint relative to fixed forms exactly when the completed
pairs are adjoint at every finite and infinite place. -/
theorem rationalFunctionMatrix_isAdjointPair_iff_forall_place
    (F : Type u) [Field F] [Finite F] {m : Type w} {n : Type x} [Fintype m] [Fintype n]
    (J : Matrix n n (RatFunc F)) (J' : Matrix m m (RatFunc F))
    (A : Matrix m n (RatFunc F)) (A' : Matrix n m (RatFunc F)) :
    Matrix.IsAdjointPair J J' A A' ↔ ∀ p : RationalFunctionPlace F,
      Matrix.IsAdjointPair (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (J'.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (A.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (A'.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  constructor
  · intro h p
    exact (matrix_isAdjointPair_iff_map (L := rationalFunctionCompletion F p) J J' A A').mp h
  · intro h
    exact (matrix_isAdjointPair_iff_map
      (L := rationalFunctionCompletion F .infinite) J J' A A').mpr (h .infinite)

/-- A number-field matrix is self-adjoint relative to a fixed form exactly when all completed
matrices are self-adjoint relative to the completed form. -/
theorem numberFieldMatrix_isSelfAdjoint_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n]
    (J A : Matrix n n K) :
    J.IsSelfAdjoint A ↔ ∀ p : NumberFieldPlace K,
      (J.map (algebraMap K (completion K p))).IsSelfAdjoint
        (A.map (algebraMap K (completion K p))) := by
  constructor
  · intro h p
    exact (matrix_isSelfAdjoint_iff_map (L := completion K p) J A).mp h
  · intro h
    exact (matrix_isSelfAdjoint_iff_map (L := completion K (witnessPlace K)) J A).mpr
      (h (witnessPlace K))

/-- An `F(t)`-matrix is self-adjoint relative to a fixed form exactly when all completed matrices
are self-adjoint relative to the completed form. -/
theorem rationalFunctionMatrix_isSelfAdjoint_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n]
    (J A : Matrix n n (RatFunc F)) :
    J.IsSelfAdjoint A ↔ ∀ p : RationalFunctionPlace F,
      (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).IsSelfAdjoint
        (A.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  constructor
  · intro h p
    exact (matrix_isSelfAdjoint_iff_map (L := rationalFunctionCompletion F p) J A).mp h
  · intro h
    exact (matrix_isSelfAdjoint_iff_map
      (L := rationalFunctionCompletion F .infinite) J A).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
