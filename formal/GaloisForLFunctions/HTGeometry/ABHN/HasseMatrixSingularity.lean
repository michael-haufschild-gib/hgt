import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialEvaluation

/-!
# Hasse detection for matrix singularity

For a square matrix over a global field, its determinant vanishes exactly when every completed
local determinant vanishes. Equivalently, a globally specified finite linear system is nonsingular
exactly when its scalar extension is nonsingular at every place. This detects a global matrix under
localization; it does not assert that independently chosen local linear systems descend globally.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-- A square matrix over a number field is singular exactly when its scalar extension is singular
at every completed place. -/
theorem numberFieldMatrix_det_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M.det = 0 ↔ ∀ v : NumberFieldPlace K, (M.map (placeEmbedding K v)).det = 0 := by
  constructor
  · intro h v
    simpa only [RingHom.mapMatrix_apply, h, map_zero] using
      ((placeEmbedding K v).map_det M).symm
  · intro h
    apply (placeEmbedding K (witnessPlace K)).injective
    have hw := h (witnessPlace K)
    calc
      placeEmbedding K (witnessPlace K) M.det =
          ((placeEmbedding K (witnessPlace K)).mapMatrix M).det :=
        (placeEmbedding K (witnessPlace K)).map_det M
      _ = 0 := by simpa only [RingHom.mapMatrix_apply] using hw

/-- A square matrix over a number field is nonsingular exactly when all its completed scalar
extensions are nonsingular. -/
theorem numberFieldMatrix_det_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M.det ≠ 0 ↔ ∀ v : NumberFieldPlace K, (M.map (placeEmbedding K v)).det ≠ 0 := by
  constructor
  · intro h v hv
    apply h
    apply (placeEmbedding K v).injective
    simp only [map_zero]
    calc
      placeEmbedding K v M.det = ((placeEmbedding K v).mapMatrix M).det :=
        (placeEmbedding K v).map_det M
      _ = 0 := by simpa only [RingHom.mapMatrix_apply] using hv
  · intro h hzero
    exact h (witnessPlace K) (by
      simpa only [RingHom.mapMatrix_apply, hzero, map_zero] using
        ((placeEmbedding K (witnessPlace K)).map_det M).symm)

/-- A square matrix over `F(t)` is singular exactly when its scalar extension is singular at every
finite and infinite completion. -/
theorem rationalFunctionMatrix_det_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    M.det = 0 ↔ ∀ v : RationalFunctionPlace F,
      (M.map (rationalFunctionPlaceEmbedding F v)).det = 0 := by
  constructor
  · intro h v
    simpa only [RingHom.mapMatrix_apply, h, map_zero] using
      ((rationalFunctionPlaceEmbedding F v).map_det M).symm
  · intro h
    apply (rationalFunctionPlaceEmbedding F .infinite).injective
    have hw := h .infinite
    calc
      rationalFunctionPlaceEmbedding F .infinite M.det =
          ((rationalFunctionPlaceEmbedding F .infinite).mapMatrix M).det :=
        (rationalFunctionPlaceEmbedding F .infinite).map_det M
      _ = 0 := by simpa only [RingHom.mapMatrix_apply] using hw

/-- A square matrix over `F(t)` is nonsingular exactly when all its completed scalar extensions
are nonsingular. -/
theorem rationalFunctionMatrix_det_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    M.det ≠ 0 ↔ ∀ v : RationalFunctionPlace F,
      (M.map (rationalFunctionPlaceEmbedding F v)).det ≠ 0 := by
  constructor
  · intro h v hv
    apply h
    apply (rationalFunctionPlaceEmbedding F v).injective
    simp only [map_zero]
    calc
      rationalFunctionPlaceEmbedding F v M.det =
          ((rationalFunctionPlaceEmbedding F v).mapMatrix M).det :=
        (rationalFunctionPlaceEmbedding F v).map_det M
      _ = 0 := by simpa only [RingHom.mapMatrix_apply] using hv
  · intro h hzero
    exact h .infinite (by
      simpa only [RingHom.mapMatrix_apply, hzero, map_zero] using
        ((rationalFunctionPlaceEmbedding F .infinite).map_det M).symm)

/-- A specified scalar is a root of the characteristic determinant of a global number-field
matrix exactly when it is a root after scalar extension at every completion. -/
theorem numberFieldMatrix_sub_scalar_det_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (a : K) :
    (M - a • 1).det = 0 ↔ ∀ v : NumberFieldPlace K,
      (M.map (placeEmbedding K v) - placeEmbedding K v a • 1).det = 0 := by
  have hmap (v : NumberFieldPlace K) :
      (M - a • 1).map (placeEmbedding K v) =
        M.map (placeEmbedding K v) - placeEmbedding K v a • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [numberFieldMatrix_det_eq_zero_iff_forall_place]
  simp_rw [hmap]

/-- A specified rational function is a root of the characteristic determinant of a global
matrix over `F(t)` exactly when it is a root after scalar extension at every completion. -/
theorem rationalFunctionMatrix_sub_scalar_det_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (a : RatFunc F) :
    (M - a • 1).det = 0 ↔ ∀ v : RationalFunctionPlace F,
      (M.map (rationalFunctionPlaceEmbedding F v) - rationalFunctionPlaceEmbedding F v a • 1).det =
        0 := by
  have hmap (v : RationalFunctionPlace F) :
      (M - a • 1).map (rationalFunctionPlaceEmbedding F v) =
        M.map (rationalFunctionPlaceEmbedding F v) - rationalFunctionPlaceEmbedding F v a • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [rationalFunctionMatrix_det_eq_zero_iff_forall_place]
  simp_rw [hmap]

/-- A number-field matrix is singular exactly when it is singular at one completion. -/
theorem numberFieldMatrix_det_eq_zero_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M.det = 0 ↔ ∃ v : NumberFieldPlace K, (M.map (placeEmbedding K v)).det = 0 := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldMatrix_det_eq_zero_iff_forall_place K n M).mp h (witnessPlace K)⟩
  · rintro ⟨v, hv⟩
    apply (placeEmbedding K v).injective
    calc
      placeEmbedding K v M.det = ((placeEmbedding K v).mapMatrix M).det :=
        (placeEmbedding K v).map_det M
      _ = 0 := by simpa only [RingHom.mapMatrix_apply] using hv
      _ = placeEmbedding K v 0 := (map_zero _).symm

/-- A number-field matrix is nonsingular exactly when it is nonsingular at one completion. -/
theorem numberFieldMatrix_det_ne_zero_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M.det ≠ 0 ↔ ∃ v : NumberFieldPlace K, (M.map (placeEmbedding K v)).det ≠ 0 := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldMatrix_det_ne_zero_iff_forall_place K n M).mp h (witnessPlace K)⟩
  · rintro ⟨v, hv⟩ hzero
    apply hv
    simpa only [RingHom.mapMatrix_apply, hzero, map_zero] using
      ((placeEmbedding K v).map_det M).symm

/-- A rational-function-field matrix is singular exactly when it is singular at one finite or
infinite completion. -/
theorem rationalFunctionMatrix_det_eq_zero_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    M.det = 0 ↔ ∃ v : RationalFunctionPlace F,
      (M.map (rationalFunctionPlaceEmbedding F v)).det = 0 := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionMatrix_det_eq_zero_iff_forall_place F n M).mp h .infinite⟩
  · rintro ⟨v, hv⟩
    apply (rationalFunctionPlaceEmbedding F v).injective
    calc
      rationalFunctionPlaceEmbedding F v M.det =
          ((rationalFunctionPlaceEmbedding F v).mapMatrix M).det :=
        (rationalFunctionPlaceEmbedding F v).map_det M
      _ = 0 := by simpa only [RingHom.mapMatrix_apply] using hv
      _ = rationalFunctionPlaceEmbedding F v 0 := (map_zero _).symm

/-- A rational-function-field matrix is nonsingular exactly when it is nonsingular at one finite
or infinite completion. -/
theorem rationalFunctionMatrix_det_ne_zero_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    M.det ≠ 0 ↔ ∃ v : RationalFunctionPlace F,
      (M.map (rationalFunctionPlaceEmbedding F v)).det ≠ 0 := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionMatrix_det_ne_zero_iff_forall_place F n M).mp h .infinite⟩
  · rintro ⟨v, hv⟩ hzero
    apply hv
    simpa only [RingHom.mapMatrix_apply, hzero, map_zero] using
      ((rationalFunctionPlaceEmbedding F v).map_det M).symm

/-- A specified scalar is a characteristic root of a number-field matrix exactly when it is a
root at one completion. -/
theorem numberFieldMatrix_sub_scalar_det_eq_zero_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (a : K) :
    (M - a • 1).det = 0 ↔ ∃ v : NumberFieldPlace K,
      (M.map (placeEmbedding K v) - placeEmbedding K v a • 1).det = 0 := by
  have hmap (v : NumberFieldPlace K) :
      (M - a • 1).map (placeEmbedding K v) =
        M.map (placeEmbedding K v) - placeEmbedding K v a • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [numberFieldMatrix_det_eq_zero_iff_exists_place]
  simp_rw [hmap]

/-- A specified rational function is a characteristic root of a global matrix exactly when it is
a root at one finite or infinite completion. -/
theorem rationalFunctionMatrix_sub_scalar_det_eq_zero_iff_exists_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (a : RatFunc F) :
    (M - a • 1).det = 0 ↔ ∃ v : RationalFunctionPlace F,
      (M.map (rationalFunctionPlaceEmbedding F v) -
        rationalFunctionPlaceEmbedding F v a • 1).det = 0 := by
  have hmap (v : RationalFunctionPlace F) :
      (M - a • 1).map (rationalFunctionPlaceEmbedding F v) =
        M.map (rationalFunctionPlaceEmbedding F v) -
          rationalFunctionPlaceEmbedding F v a • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [rationalFunctionMatrix_det_eq_zero_iff_exists_place]
  simp_rw [hmap]

end GaloisForLFunctions.HTGeometry.ABHN
