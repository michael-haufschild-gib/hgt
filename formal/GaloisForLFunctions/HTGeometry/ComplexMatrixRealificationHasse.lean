import GaloisForLFunctions.HTGeometry.ComplexEventSquareRealificationNoGo

/-!
# Hasse reconstruction through complex-matrix realification

The doubled-real block representation is a faithful scalar-transfer chart for complex matrices.
This file packages faithfulness as coordinatewise local-to-global reconstruction.  It also proves
that the upper-left real block and lower-left imaginary block already form a complete local atlas;
the other two blocks are redundant.

Thus real positivity, Gram, or inertia arguments may consume complex operator data through a real
model without losing distinctions.  The theorem supplies infrastructure only: a route must still
prove that its analytic or arithmetic source produces the relevant matrix.
-/

open Matrix
open scoped Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

universe u v

variable {m : Type u} {n : Type v}

/-- Complex matrices are equivalent to the doubled-real matrices they realize. -/
noncomputable def complexMatrixRealificationHasseEquivRange :
    Matrix m n ℂ ≃ Set.range
      (complexMatrixRealification : Matrix m n ℂ → Matrix (m ⊕ m) (n ⊕ n) ℝ) :=
  Equiv.ofInjective complexMatrixRealification complexMatrixRealification_injective

@[simp]
theorem complexMatrixRealificationHasseEquivRange_apply (X : Matrix m n ℂ) :
    (complexMatrixRealificationHasseEquivRange X : Matrix (m ⊕ m) (n ⊕ n) ℝ) =
      complexMatrixRealification X := rfl

/-- Complex matrices agree exactly when all doubled-real local entries agree. -/
theorem complexMatrix_congr_realification_hasse_iff (X Y : Matrix m n ℂ) :
    X = Y ↔ ∀ i j,
      complexMatrixRealification X i j = complexMatrixRealification Y i j := by
  constructor
  · rintro rfl
    exact fun _ _ ↦ rfl
  · intro h
    apply complexMatrixRealification_injective
    funext i j
    exact h i j

/-- Only the real and imaginary first-column blocks are needed for reconstruction. -/
theorem complexMatrix_congr_twoBlock_hasse_iff (X Y : Matrix m n ℂ) :
    X = Y ↔
      (∀ i j,
        complexMatrixRealification X (Sum.inl i) (Sum.inl j) =
          complexMatrixRealification Y (Sum.inl i) (Sum.inl j)) ∧
      (∀ i j,
        complexMatrixRealification X (Sum.inr i) (Sum.inl j) =
          complexMatrixRealification Y (Sum.inr i) (Sum.inl j)) := by
  constructor
  · rintro rfl
    exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  · rintro ⟨hre, him⟩
    ext i j
    apply Complex.ext
    · simpa [complexMatrixRealification, complexMatrixRealPart] using hre i j
    · simpa [complexMatrixRealification, complexMatrixImagPart] using him i j

/-- A nonzero complex matrix has a nonzero real or imaginary local block entry. -/
theorem exists_realification_twoBlock_ne_zero_of_ne_zero
    (X : Matrix m n ℂ) (hX : X ≠ 0) :
    ∃ i j,
      complexMatrixRealification X (Sum.inl i) (Sum.inl j) ≠ 0 ∨
      complexMatrixRealification X (Sum.inr i) (Sum.inl j) ≠ 0 := by
  by_contra h
  push Not at h
  apply hX
  apply (complexMatrix_congr_twoBlock_hasse_iff X 0).2
  constructor
  · intro i j
    simpa [complexMatrixRealification, complexMatrixRealPart] using h i j |>.1
  · intro i j
    simpa [complexMatrixRealification, complexMatrixImagPart] using h i j |>.2

end GaloisForLFunctions.HTGeometry
