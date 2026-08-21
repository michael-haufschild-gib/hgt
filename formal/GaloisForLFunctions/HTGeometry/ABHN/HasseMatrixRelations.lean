/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixEquations

/-!
# Hasse detection of matrix relations

Field scalar extension reflects polynomial and intertwining relations between specified square
matrices.  Thus finite-order symmetries, idempotent projectors, commutation, and a fixed matrix
semiconjugacy relation can each be certified at every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- A prescribed matrix power is the identity exactly when its coefficientwise scalar extension
has that property. -/
theorem matrix_pow_eq_one_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (d : ℕ) :
    M ^ d = 1 ↔ (M.map (algebraMap K L)) ^ d = 1 := by
  constructor
  · intro h
    rw [← Matrix.map_pow, h]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · intro h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (M ^ d).map (algebraMap K L) = (1 : Matrix n n K).map (algebraMap K L)
    rw [Matrix.map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
    exact h

/-- A specified matrix is idempotent exactly when its coefficientwise scalar extension is
idempotent. -/
theorem matrix_isIdempotentElem_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    IsIdempotentElem M ↔ IsIdempotentElem (M.map (algebraMap K L)) := by
  change M * M = M ↔ M.map (algebraMap K L) * M.map (algebraMap K L) = M.map (algebraMap K L)
  constructor
  · intro h
    rw [← Matrix.map_mul]
    exact congrArg (fun N => N.map (algebraMap K L)) h
  · intro h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (M * M).map (algebraMap K L) = M.map (algebraMap K L)
    rw [Matrix.map_mul]
    exact h

/-- Two specified matrices commute exactly when their coefficientwise scalar extensions commute.
-/
theorem matrix_commute_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M N : Matrix n n K) :
    Commute M N ↔ Commute (M.map (algebraMap K L)) (N.map (algebraMap K L)) := by
  change M * N = N * M ↔ M.map (algebraMap K L) * N.map (algebraMap K L) =
    N.map (algebraMap K L) * M.map (algebraMap K L)
  constructor
  · intro h
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun X => X.map (algebraMap K L)) h
  · intro h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (M * N).map (algebraMap K L) = (N * M).map (algebraMap K L)
    rw [Matrix.map_mul, Matrix.map_mul]
    exact h

/-- A specified matrix semiconjugacy relation is reflected by coefficientwise scalar extension. -/
theorem matrix_semiconjBy_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (A X Y : Matrix n n K) :
    SemiconjBy A X Y ↔ SemiconjBy (A.map (algebraMap K L))
      (X.map (algebraMap K L)) (Y.map (algebraMap K L)) := by
  change A * X = Y * A ↔ A.map (algebraMap K L) * X.map (algebraMap K L) =
    Y.map (algebraMap K L) * A.map (algebraMap K L)
  constructor
  · intro h
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun Z => Z.map (algebraMap K L)) h
  · intro h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (A * X).map (algebraMap K L) = (Y * A).map (algebraMap K L)
    rw [Matrix.map_mul, Matrix.map_mul]
    exact h

/-- A number-field matrix has prescribed finite order exactly when each completed matrix does. -/
theorem numberFieldMatrix_pow_eq_one_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (d : ℕ) :
    M ^ d = 1 ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))) ^ d = 1 := by
  constructor
  · intro h p
    exact (matrix_pow_eq_one_iff_map (L := completion K p) M d).mp h
  · intro h
    exact (matrix_pow_eq_one_iff_map (L := completion K (witnessPlace K)) M d).mpr
      (h (witnessPlace K))

/-- A rational-function-field matrix has prescribed finite order exactly when every finite and
infinite completed matrix does. -/
theorem rationalFunctionMatrix_pow_eq_one_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (d : ℕ) :
    M ^ d = 1 ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) ^ d = 1 := by
  constructor
  · intro h p
    exact (matrix_pow_eq_one_iff_map (L := rationalFunctionCompletion F p) M d).mp h
  · intro h
    exact (matrix_pow_eq_one_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) M d).mpr
      (h RationalFunctionPlace.infinite)

/-- A number-field matrix is an idempotent projector exactly when every completed matrix is. -/
theorem numberFieldMatrix_isIdempotentElem_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    IsIdempotentElem M ↔ ∀ p : NumberFieldPlace K,
      IsIdempotentElem (M.map (algebraMap K (completion K p))) := by
  constructor
  · intro h p
    exact (matrix_isIdempotentElem_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_isIdempotentElem_iff_map (L := completion K (witnessPlace K)) M).mpr
      (h (witnessPlace K))

/-- A rational-function-field matrix is an idempotent projector exactly when every finite and
infinite completed matrix is. -/
theorem rationalFunctionMatrix_isIdempotentElem_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    IsIdempotentElem M ↔ ∀ p : RationalFunctionPlace F,
      IsIdempotentElem (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  constructor
  · intro h p
    exact (matrix_isIdempotentElem_iff_map (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_isIdempotentElem_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) M).mpr
      (h RationalFunctionPlace.infinite)

/-- Two number-field matrices commute exactly when all corresponding completed matrices commute.
-/
theorem numberFieldMatrix_commute_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M N : Matrix n n K) :
    Commute M N ↔ ∀ p : NumberFieldPlace K,
      Commute (M.map (algebraMap K (completion K p))) (N.map (algebraMap K (completion K p))) := by
  constructor
  · intro h p
    exact (matrix_commute_iff_map (L := completion K p) M N).mp h
  · intro h
    exact (matrix_commute_iff_map (L := completion K (witnessPlace K)) M N).mpr
      (h (witnessPlace K))

/-- Two rational-function-field matrices commute exactly when all finite and infinite completed
matrices commute. -/
theorem rationalFunctionMatrix_commute_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M N : Matrix n n (RatFunc F)) :
    Commute M N ↔ ∀ p : RationalFunctionPlace F,
      Commute (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (N.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  constructor
  · intro h p
    exact (matrix_commute_iff_map (L := rationalFunctionCompletion F p) M N).mp h
  · intro h
    exact (matrix_commute_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) M N).mpr
      (h RationalFunctionPlace.infinite)

/-- A specified number-field matrix semiconjugacy relation holds exactly when it holds after
every completed scalar extension. -/
theorem numberFieldMatrix_semiconjBy_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (A X Y : Matrix n n K) :
    SemiconjBy A X Y ↔ ∀ p : NumberFieldPlace K,
      SemiconjBy (A.map (algebraMap K (completion K p)))
        (X.map (algebraMap K (completion K p))) (Y.map (algebraMap K (completion K p))) := by
  constructor
  · intro h p
    exact (matrix_semiconjBy_iff_map (L := completion K p) A X Y).mp h
  · intro h
    exact (matrix_semiconjBy_iff_map (L := completion K (witnessPlace K)) A X Y).mpr
      (h (witnessPlace K))

/-- A specified rational-function-field matrix semiconjugacy relation holds exactly when it holds
after every finite and infinite completed scalar extension. -/
theorem rationalFunctionMatrix_semiconjBy_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (A X Y : Matrix n n (RatFunc F)) :
    SemiconjBy A X Y ↔ ∀ p : RationalFunctionPlace F,
      SemiconjBy (A.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (X.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (Y.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  constructor
  · intro h p
    exact (matrix_semiconjBy_iff_map (L := rationalFunctionCompletion F p) A X Y).mp h
  · intro h
    exact (matrix_semiconjBy_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) A X Y).mpr
      (h RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
