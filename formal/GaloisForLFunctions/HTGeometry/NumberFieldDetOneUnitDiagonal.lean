import GaloisForLFunctions.HTGeometry.NumberFieldDetOneUnitPlaceLogCovering

/-!
# Determinant-one unit diagonal matrices

A tuple of number-ring units with product one gives a literal special-linear diagonal matrix.
This is the integral congruence witness consumed by unit balancing in number-field reduction.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- Diagonal matrix with prescribed number-ring units. -/
def numberFieldUnitDiagonal (u : Fin n → (𝓞 K)ˣ) :
    Matrix (Fin n) (Fin n) (𝓞 K) :=
  Matrix.diagonal fun i => (u i : 𝓞 K)

theorem det_numberFieldUnitDiagonal (u : Fin n → (𝓞 K)ˣ) :
    (numberFieldUnitDiagonal u).det = ((∏ i, u i : (𝓞 K)ˣ) : 𝓞 K) := by
  simp [numberFieldUnitDiagonal]

theorem det_numberFieldUnitDiagonal_eq_one
    (u : Fin n → (𝓞 K)ˣ) (hu : ∏ i, u i = 1) :
    (numberFieldUnitDiagonal u).det = 1 := by
  rw [det_numberFieldUnitDiagonal, hu]
  rfl

/-- A product-one unit tuple as an element of `SLₙ(𝓞 K)`. -/
def numberFieldUnitSpecialLinear
    (u : Fin n → (𝓞 K)ˣ) (hu : ∏ i, u i = 1) :
    Matrix.SpecialLinearGroup (Fin n) (𝓞 K) :=
  ⟨numberFieldUnitDiagonal u, det_numberFieldUnitDiagonal_eq_one u hu⟩

@[simp]
theorem numberFieldUnitDiagonal_mulVec
    (u : Fin n → (𝓞 K)ˣ) (x : Fin n → 𝓞 K) (i : Fin n) :
    (numberFieldUnitDiagonal u *ᵥ x) i = (u i : 𝓞 K) * x i := by
  classical
  rw [numberFieldUnitDiagonal, Matrix.mulVec, dotProduct,
    Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Matrix.diagonal, Ne.symm hji]
  · simp

end

end GaloisForLFunctions.HTGeometry
