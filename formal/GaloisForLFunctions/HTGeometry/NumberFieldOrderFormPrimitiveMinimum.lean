import GaloisForLFunctions.HTGeometry.NumberFieldPositiveFormPrimitiveMinimum
import GaloisForLFunctions.HTGeometry.OrderSymmetricSpace

/-!
# Primitive minima for number-field order forms

Every point of the positive balanced order cone determines a quadratic form on canonical mixed
coordinates.  This file produces its primitive algebraic-integer minimizer and determinant-one
completion without retaining a positive-definiteness, frame, lattice, or minimum hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical NumberField

noncomputable section

/-- Every positive balanced order form has a primitive algebraic-integer minimizer that extends to
the first column of a determinant-one matrix. -/
theorem exists_numberFieldInteger_minimalPrimitiveVector_orderForm
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 2 ≤ n)
    (A : ↥(orderCone (nb := n) (numberFieldIntegerBasis K))) :
    ∃ (a : Fin n → 𝓞 K) (β : Matrix (Fin n) (Fin n) (𝓞 K)),
      (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
      (∀ b : Fin n → 𝓞 K,
        (∃ p : Fin n → 𝓞 K, ∑ i, p i * b i = 1) →
        let c := numberFieldMixedVectorContinuousLinearEquiv K n
        let M := ((A : orderForms (nb := n) (numberFieldIntegerBasis K)) :
          Matrix (Fin (n * Module.finrank ℚ K))
            (Fin (n * Module.finrank ℚ K)) ℝ)
        c (numberFieldIntegerVectorEmbedding K a) ⬝ᵥ
            M.mulVec (c (numberFieldIntegerVectorEmbedding K a)) ≤
          c (numberFieldIntegerVectorEmbedding K b) ⬝ᵥ
            M.mulVec (c (numberFieldIntegerVectorEmbedding K b))) ∧
      β.det = 1 ∧
      ∀ i, β i ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ = a i := by
  exact exists_numberFieldInteger_minimalPrimitiveVector_posDef K n hn
    (((A : orderForms (nb := n) (numberFieldIntegerBasis K)) :
      Matrix (Fin (n * Module.finrank ℚ K))
        (Fin (n * Module.finrank ℚ K)) ℝ)) A.2

end

end GaloisForLFunctions.HTGeometry
