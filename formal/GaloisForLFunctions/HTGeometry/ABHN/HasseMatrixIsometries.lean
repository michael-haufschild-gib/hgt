import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRelations

/-!
# Hasse detection for form-preserving matrices

Preservation of a fixed bilinear form is the matrix equation `Mᵀ * J * M = J`.  Coefficientwise
field scalar extension reflects this equation, so a prescribed orthogonal or symplectic structure
can be checked at every completion.

This concerns a fixed global form `J`; it does not assert a Hasse principle for patching
independently chosen local forms.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- A matrix preserves a specified bilinear form exactly when its coefficientwise scalar extension
does. -/
theorem matrix_preservesForm_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (J M : Matrix n n K) :
    M.transpose * J * M = J ↔
      (M.map (algebraMap K L)).transpose * (J.map (algebraMap K L)) *
          M.map (algebraMap K L) = J.map (algebraMap K L) := by
  constructor
  · intro h
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]
  · intro h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (M.transpose * J * M).map (algebraMap K L) = J.map (algebraMap K L)
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    exact h

/-- A matrix lies in the infinitesimal stabilizer of a specified bilinear form exactly when its
coefficientwise scalar extension does. -/
theorem matrix_infinitesimallyPreservesForm_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (J M : Matrix n n K) :
    M.transpose * J + J * M = 0 ↔
      (M.map (algebraMap K L)).transpose * (J.map (algebraMap K L)) +
          (J.map (algebraMap K L)) * M.map (algebraMap K L) = 0 := by
  constructor
  · intro h
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_add (algebraMap K L) (map_add _), h,
      Matrix.map_zero (algebraMap K L) (map_zero _)]
  · intro h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (M.transpose * J + J * M).map (algebraMap K L) =
      (0 : Matrix n n K).map (algebraMap K L)
    rw [Matrix.map_add (algebraMap K L) (map_add _), Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, Matrix.map_zero (algebraMap K L) (map_zero _)]
    exact h

/-- A number-field matrix preserves a specified bilinear form exactly when all its completed
scalar extensions preserve the corresponding completed form. -/
theorem numberFieldMatrix_preservesForm_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n K) :
    M.transpose * J * M = J ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).transpose *
          (J.map (algebraMap K (completion K p))) *
          M.map (algebraMap K (completion K p)) = J.map (algebraMap K (completion K p)) := by
  constructor
  · intro h p
    exact (matrix_preservesForm_iff_map (L := completion K p) J M).mp h
  · intro h
    exact (matrix_preservesForm_iff_map (L := completion K (witnessPlace K)) J M).mpr
      (h (witnessPlace K))

/-- A number-field matrix lies in the infinitesimal stabilizer of a specified bilinear form
exactly when every completed scalar extension does. -/
theorem numberFieldMatrix_infinitesimallyPreservesForm_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n K) :
    M.transpose * J + J * M = 0 ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).transpose *
          (J.map (algebraMap K (completion K p))) +
          (J.map (algebraMap K (completion K p))) *
            M.map (algebraMap K (completion K p)) = 0 := by
  constructor
  · intro h p
    exact (matrix_infinitesimallyPreservesForm_iff_map (L := completion K p) J M).mp h
  · intro h
    exact (matrix_infinitesimallyPreservesForm_iff_map
      (L := completion K (witnessPlace K)) J M).mpr (h (witnessPlace K))

/-- An `F(t)`-matrix preserves a specified bilinear form exactly when all finite and infinite
completed scalar extensions preserve the corresponding completed form. -/
theorem rationalFunctionMatrix_preservesForm_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n (RatFunc F)) :
    M.transpose * J * M = J ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).transpose *
          (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) *
          M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) =
            J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (matrix_preservesForm_iff_map (L := rationalFunctionCompletion F p) J M).mp h
  · intro h
    exact (matrix_preservesForm_iff_map
      (L := rationalFunctionCompletion F .infinite) J M).mpr (h .infinite)

/-- An `F(t)`-matrix lies in the infinitesimal stabilizer of a specified bilinear form exactly
when every finite and infinite completed scalar extension does. -/
theorem rationalFunctionMatrix_infinitesimallyPreservesForm_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n (RatFunc F)) :
    M.transpose * J + J * M = 0 ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).transpose *
          (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) +
          (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) *
            M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) = 0 := by
  constructor
  · intro h p
    exact (matrix_infinitesimallyPreservesForm_iff_map
      (L := rationalFunctionCompletion F p) J M).mp h
  · intro h
    exact (matrix_infinitesimallyPreservesForm_iff_map
      (L := rationalFunctionCompletion F .infinite) J M).mpr (h .infinite)

/-- Preservation of a fixed form by a number-field matrix can be certified at one completion. -/
theorem numberFieldMatrix_preservesForm_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n K) :
    M.transpose * J * M = J ↔ ∃ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).transpose *
          (J.map (algebraMap K (completion K p))) *
          M.map (algebraMap K (completion K p)) = J.map (algebraMap K (completion K p)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (matrix_preservesForm_iff_map (L := completion K (witnessPlace K)) J M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_preservesForm_iff_map (L := completion K p) J M).mpr hp

/-- Preservation of a fixed form by an `F(t)`-matrix can be certified at one completion. -/
theorem rationalFunctionMatrix_preservesForm_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n (RatFunc F)) :
    M.transpose * J * M = J ↔ ∃ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).transpose *
          (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) *
          M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) =
            J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (matrix_preservesForm_iff_map
        (L := rationalFunctionCompletion F .infinite) J M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_preservesForm_iff_map (L := rationalFunctionCompletion F p) J M).mpr hp

/-- Infinitesimal preservation of a fixed form by a number-field matrix can be certified at one
completion. -/
theorem numberFieldMatrix_infinitesimallyPreservesForm_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n K) :
    M.transpose * J + J * M = 0 ↔ ∃ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).transpose *
          (J.map (algebraMap K (completion K p))) +
          (J.map (algebraMap K (completion K p))) *
            M.map (algebraMap K (completion K p)) = 0 := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (matrix_infinitesimallyPreservesForm_iff_map
        (L := completion K (witnessPlace K)) J M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_infinitesimallyPreservesForm_iff_map (L := completion K p) J M).mpr hp

/-- Infinitesimal preservation of a fixed form by an `F(t)`-matrix can be certified at one
completion. -/
theorem rationalFunctionMatrix_infinitesimallyPreservesForm_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n (RatFunc F)) :
    M.transpose * J + J * M = 0 ↔ ∃ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).transpose *
          (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) +
          (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) *
            M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) = 0 := by
  constructor
  · intro h
    exact ⟨.infinite,
      (matrix_infinitesimallyPreservesForm_iff_map
        (L := rationalFunctionCompletion F .infinite) J M).mp h⟩
  · rintro ⟨p, hp⟩
    exact (matrix_infinitesimallyPreservesForm_iff_map
      (L := rationalFunctionCompletion F p) J M).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
