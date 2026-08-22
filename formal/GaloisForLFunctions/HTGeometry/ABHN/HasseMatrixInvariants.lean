/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixSingularity
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Hasse detection for prescribed matrix invariants

Characteristic polynomials and determinants commute with coefficientwise field scalar extension.
Thus equality with a fixed global polynomial or scalar is detectable at every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- Equality of a matrix characteristic polynomial with a specified polynomial is reflected by
field scalar extension. -/
theorem matrix_charpoly_eq_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (p : Polynomial K) :
    M.charpoly = p ↔ (M.map (algebraMap K L)).charpoly = p.map (algebraMap K L) := by
  rw [Matrix.charpoly_map]
  constructor
  · intro h
    rw [h]
  · intro h
    apply Polynomial.map_injective (algebraMap K L) (FaithfulSMul.algebraMap_injective K L)
    exact h

/-- Equality of a matrix determinant with a specified scalar is reflected by field scalar
extension. -/
theorem matrix_det_eq_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (c : K) :
    M.det = c ↔ (M.map (algebraMap K L)).det = algebraMap K L c := by
  constructor
  · intro h
    calc
      (M.map (algebraMap K L)).det = algebraMap K L M.det := by
        simpa only [RingHom.mapMatrix_apply] using ((algebraMap K L).map_det M).symm
      _ = algebraMap K L c := congrArg (algebraMap K L) h
  · intro h
    apply FaithfulSMul.algebraMap_injective K L
    calc
      algebraMap K L M.det = (M.map (algebraMap K L)).det := by
        simpa only [RingHom.mapMatrix_apply] using (algebraMap K L).map_det M
      _ = algebraMap K L c := h

/-- Equality of a matrix trace with a specified scalar is reflected by field scalar extension. -/
theorem matrix_trace_eq_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n]
    (M : Matrix n n K) (c : K) :
    M.trace = c ↔ (M.map (algebraMap K L)).trace = algebraMap K L c := by
  constructor
  · intro h
    calc
      (M.map (algebraMap K L)).trace = algebraMap K L M.trace := by
        simpa only [RingHom.mapMatrix_apply] using
          (AddMonoidHom.map_trace (algebraMap K L) M).symm
      _ = algebraMap K L c := congrArg (algebraMap K L) h
  · intro h
    apply FaithfulSMul.algebraMap_injective K L
    calc
      algebraMap K L M.trace = (M.map (algebraMap K L)).trace := by
        simpa only [RingHom.mapMatrix_apply] using AddMonoidHom.map_trace (algebraMap K L) M
      _ = algebraMap K L c := h

/-- A number-field matrix has characteristic polynomial `p` exactly when every completed matrix
has the coefficientwise scalar extension of `p` as characteristic polynomial. -/
theorem numberFieldMatrix_charpoly_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (p : Polynomial K) :
    M.charpoly = p ↔ ∀ v : NumberFieldPlace K,
      (M.map (algebraMap K (completion K v))).charpoly =
        p.map (algebraMap K (completion K v)) := by
  constructor
  · intro h v
    exact (matrix_charpoly_eq_iff_map (L := completion K v) M p).mp h
  · intro h
    exact (matrix_charpoly_eq_iff_map (L := completion K (witnessPlace K)) M p).mpr
      (h (witnessPlace K))

/-- A number-field matrix has determinant `c` exactly when every completed matrix has determinant
equal to the image of `c`. -/
theorem numberFieldMatrix_det_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (c : K) :
    M.det = c ↔ ∀ v : NumberFieldPlace K,
      (M.map (algebraMap K (completion K v))).det = algebraMap K (completion K v) c := by
  constructor
  · intro h v
    exact (matrix_det_eq_iff_map (L := completion K v) M c).mp h
  · intro h
    exact (matrix_det_eq_iff_map (L := completion K (witnessPlace K)) M c).mpr
      (h (witnessPlace K))

/-- A number-field matrix has trace `c` exactly when every completed matrix has trace equal to the
image of `c`. -/
theorem numberFieldMatrix_trace_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n]
    (M : Matrix n n K) (c : K) :
    M.trace = c ↔ ∀ v : NumberFieldPlace K,
      (M.map (algebraMap K (completion K v))).trace = algebraMap K (completion K v) c := by
  constructor
  · intro h v
    exact (matrix_trace_eq_iff_map (L := completion K v) M c).mp h
  · intro h
    exact (matrix_trace_eq_iff_map (L := completion K (witnessPlace K)) M c).mpr
      (h (witnessPlace K))

/-- A matrix over `F(t)` has characteristic polynomial `p` exactly when every finite and infinite
completed matrix has the coefficientwise scalar extension of `p` as characteristic polynomial. -/
theorem rationalFunctionMatrix_charpoly_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (p : Polynomial (RatFunc F)) :
    M.charpoly = p ↔ ∀ v : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).charpoly =
        p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) := by
  constructor
  · intro h v
    exact (matrix_charpoly_eq_iff_map (L := rationalFunctionCompletion F v) M p).mp h
  · intro h
    exact (matrix_charpoly_eq_iff_map
      (L := rationalFunctionCompletion F .infinite) M p).mpr (h .infinite)

/-- A matrix over `F(t)` has determinant `c` exactly when every finite and infinite completed
matrix has determinant equal to the image of `c`. -/
theorem rationalFunctionMatrix_det_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (c : RatFunc F) :
    M.det = c ↔ ∀ v : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).det =
        algebraMap (RatFunc F) (rationalFunctionCompletion F v) c := by
  constructor
  · intro h v
    exact (matrix_det_eq_iff_map (L := rationalFunctionCompletion F v) M c).mp h
  · intro h
    exact (matrix_det_eq_iff_map
      (L := rationalFunctionCompletion F .infinite) M c).mpr (h .infinite)

/-- A matrix over `F(t)` has trace `c` exactly when every finite and infinite completed matrix has
trace equal to the image of `c`. -/
theorem rationalFunctionMatrix_trace_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n]
    (M : Matrix n n (RatFunc F)) (c : RatFunc F) :
    M.trace = c ↔ ∀ v : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).trace =
        algebraMap (RatFunc F) (rationalFunctionCompletion F v) c := by
  constructor
  · intro h v
    exact (matrix_trace_eq_iff_map (L := rationalFunctionCompletion F v) M c).mp h
  · intro h
    exact (matrix_trace_eq_iff_map
      (L := rationalFunctionCompletion F .infinite) M c).mpr (h .infinite)

/-- A prescribed characteristic polynomial of a number-field matrix can be certified at one
completion. -/
theorem numberFieldMatrix_charpoly_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (p : Polynomial K) :
    M.charpoly = p ↔ ∃ v : NumberFieldPlace K,
      (M.map (algebraMap K (completion K v))).charpoly =
        p.map (algebraMap K (completion K v)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (matrix_charpoly_eq_iff_map (L := completion K (witnessPlace K)) M p).mp h⟩
  · rintro ⟨v, hv⟩
    exact (matrix_charpoly_eq_iff_map (L := completion K v) M p).mpr hv

/-- A prescribed determinant of a number-field matrix can be certified at one completion. -/
theorem numberFieldMatrix_det_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (c : K) :
    M.det = c ↔ ∃ v : NumberFieldPlace K,
      (M.map (algebraMap K (completion K v))).det = algebraMap K (completion K v) c := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (matrix_det_eq_iff_map (L := completion K (witnessPlace K)) M c).mp h⟩
  · rintro ⟨v, hv⟩
    exact (matrix_det_eq_iff_map (L := completion K v) M c).mpr hv

/-- A prescribed trace of a number-field matrix can be certified at one completion. -/
theorem numberFieldMatrix_trace_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n]
    (M : Matrix n n K) (c : K) :
    M.trace = c ↔ ∃ v : NumberFieldPlace K,
      (M.map (algebraMap K (completion K v))).trace = algebraMap K (completion K v) c := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (matrix_trace_eq_iff_map (L := completion K (witnessPlace K)) M c).mp h⟩
  · rintro ⟨v, hv⟩
    exact (matrix_trace_eq_iff_map (L := completion K v) M c).mpr hv

/-- A prescribed characteristic polynomial of an `F(t)`-matrix can be certified at one
completion. -/
theorem rationalFunctionMatrix_charpoly_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (p : Polynomial (RatFunc F)) :
    M.charpoly = p ↔ ∃ v : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).charpoly =
        p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (matrix_charpoly_eq_iff_map (L := rationalFunctionCompletion F .infinite) M p).mp h⟩
  · rintro ⟨v, hv⟩
    exact (matrix_charpoly_eq_iff_map (L := rationalFunctionCompletion F v) M p).mpr hv

/-- A prescribed determinant of an `F(t)`-matrix can be certified at one completion. -/
theorem rationalFunctionMatrix_det_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (c : RatFunc F) :
    M.det = c ↔ ∃ v : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).det =
        algebraMap (RatFunc F) (rationalFunctionCompletion F v) c := by
  constructor
  · intro h
    exact ⟨.infinite,
      (matrix_det_eq_iff_map (L := rationalFunctionCompletion F .infinite) M c).mp h⟩
  · rintro ⟨v, hv⟩
    exact (matrix_det_eq_iff_map (L := rationalFunctionCompletion F v) M c).mpr hv

/-- A prescribed trace of an `F(t)`-matrix can be certified at one completion. -/
theorem rationalFunctionMatrix_trace_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n]
    (M : Matrix n n (RatFunc F)) (c : RatFunc F) :
    M.trace = c ↔ ∃ v : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).trace =
        algebraMap (RatFunc F) (rationalFunctionCompletion F v) c := by
  constructor
  · intro h
    exact ⟨.infinite,
      (matrix_trace_eq_iff_map (L := rationalFunctionCompletion F .infinite) M c).mp h⟩
  · rintro ⟨v, hv⟩
    exact (matrix_trace_eq_iff_map (L := rationalFunctionCompletion F v) M c).mpr hv

end GaloisForLFunctions.HTGeometry.ABHN
