import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRelations

/-!
# Hasse detection for nilpotent matrices

Coefficientwise scalar extension reflects vanishing of a matrix power.  Consequently a matrix
over a global field is nilpotent exactly when every completed matrix is nilpotent.  This is a
local-global detector for nilpotent monodromy and degeneration operators; it does not claim that
arbitrary independently chosen local nilpotent matrices descend to one global matrix.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- Vanishing of a specified matrix power is reflected by coefficientwise field scalar extension. -/
theorem matrix_pow_eq_zero_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (d : ℕ) :
    M ^ d = 0 ↔ (M.map (algebraMap K L)) ^ d = 0 := by
  constructor
  · intro h
    rw [← Matrix.map_pow, h]
    simp
  · intro h
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective K L)
    change (M ^ d).map (algebraMap K L) = (0 : Matrix n n K).map (algebraMap K L)
    rw [Matrix.map_pow]
    simpa using h

/-- Nilpotence of a square matrix is reflected by coefficientwise field scalar extension. -/
theorem matrix_isNilpotent_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    IsNilpotent M ↔ IsNilpotent (M.map (algebraMap K L)) := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, (matrix_pow_eq_zero_iff_map (L := L) M d).mp hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, (matrix_pow_eq_zero_iff_map (L := L) M d).mpr hd⟩

/-- A prescribed power of a number-field matrix vanishes exactly when it vanishes at every
completion. -/
theorem numberFieldMatrix_pow_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (d : ℕ) :
    M ^ d = 0 ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))) ^ d = 0 := by
  constructor
  · intro h p
    exact (matrix_pow_eq_zero_iff_map (L := completion K p) M d).mp h
  · intro h
    exact (matrix_pow_eq_zero_iff_map (L := completion K (witnessPlace K)) M d).mpr
      (h (witnessPlace K))

/-- A prescribed power of an `F(t)`-matrix vanishes exactly when it vanishes at every finite and
infinite completion. -/
theorem rationalFunctionMatrix_pow_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (d : ℕ) :
    M ^ d = 0 ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) ^ d = 0 := by
  constructor
  · intro h p
    exact (matrix_pow_eq_zero_iff_map (L := rationalFunctionCompletion F p) M d).mp h
  · intro h
    exact (matrix_pow_eq_zero_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) M d).mpr
      (h RationalFunctionPlace.infinite)

/-- A specified unipotence exponent is reflected by coefficientwise field scalar extension. -/
theorem matrix_sub_one_pow_eq_zero_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (d : ℕ) :
    (M - 1) ^ d = 0 ↔ (M.map (algebraMap K L) - 1) ^ d = 0 := by
  have hmap : (M - 1).map (algebraMap K L) = M.map (algebraMap K L) - 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [← hmap]
  exact matrix_pow_eq_zero_iff_map (L := L) (M - 1) d

/-- A prescribed unipotence exponent for a number-field matrix is detected at every completion. -/
theorem numberFieldMatrix_sub_one_pow_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (d : ℕ) :
    (M - 1) ^ d = 0 ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p)) - 1) ^ d = 0 := by
  constructor
  · intro h p
    exact (matrix_sub_one_pow_eq_zero_iff_map (L := completion K p) M d).mp h
  · intro h
    exact (matrix_sub_one_pow_eq_zero_iff_map (L := completion K (witnessPlace K)) M d).mpr
      (h (witnessPlace K))

/-- A prescribed unipotence exponent for an `F(t)`-matrix is detected at all finite and infinite
completions. -/
theorem rationalFunctionMatrix_sub_one_pow_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (d : ℕ) :
    (M - 1) ^ d = 0 ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) - 1) ^ d = 0 := by
  constructor
  · intro h p
    exact (matrix_sub_one_pow_eq_zero_iff_map
      (L := rationalFunctionCompletion F p) M d).mp h
  · intro h
    exact (matrix_sub_one_pow_eq_zero_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) M d).mpr
      (h RationalFunctionPlace.infinite)

/-- A number-field matrix is nilpotent exactly when every completed matrix is nilpotent. -/
theorem numberFieldMatrix_isNilpotent_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    IsNilpotent M ↔ ∀ p : NumberFieldPlace K,
      IsNilpotent (M.map (algebraMap K (completion K p))) := by
  constructor
  · intro h p
    exact (matrix_isNilpotent_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_isNilpotent_iff_map (L := completion K (witnessPlace K)) M).mpr
      (h (witnessPlace K))

/-- A rational-function-field matrix is nilpotent exactly when its matrix at every finite and
infinite completion is nilpotent. -/
theorem rationalFunctionMatrix_isNilpotent_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    IsNilpotent M ↔ ∀ p : RationalFunctionPlace F,
      IsNilpotent (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  constructor
  · intro h p
    exact (matrix_isNilpotent_iff_map (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_isNilpotent_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) M).mpr
      (h RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
