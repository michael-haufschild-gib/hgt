import GaloisForLFunctions.HTGeometry.JacobiPositiveFrame
import GaloisForLFunctions.HTGeometry.NumberFieldMixedVectorCoordinates

/-!
# Primitive minima of positive forms over number rings

Every positive-definite real quadratic form on canonical mixed coordinates attains its minimum on
primitive vectors over a number ring.  The minimizing vector extends to the first column of a
determinant-one integral matrix.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical NumberField

noncomputable section

/-- A positive-definite form on canonical mixed coordinates has a primitive number-ring minimizer,
which extends to a determinant-one matrix. -/
theorem exists_numberFieldInteger_minimalPrimitiveVector_posDef
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin (n * Module.finrank ℚ K))
      (Fin (n * Module.finrank ℚ K)) ℝ)
    (hA : A.PosDef) :
    ∃ (a : Fin n → 𝓞 K) (β : Matrix (Fin n) (Fin n) (𝓞 K)),
      (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
      (∀ b : Fin n → 𝓞 K,
        (∃ p : Fin n → 𝓞 K, ∑ i, p i * b i = 1) →
        let ca := numberFieldMixedVectorContinuousLinearEquiv K n
          (numberFieldIntegerVectorEmbedding K a)
        let cb := numberFieldMixedVectorContinuousLinearEquiv K n
          (numberFieldIntegerVectorEmbedding K b)
        ca ⬝ᵥ A.mulVec ca ≤ cb ⬝ᵥ A.mulVec cb) ∧
      β.det = 1 ∧
      ∀ i, β i ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ = a i := by
  rcases exists_posDefContinuousLinearEquiv A hA with ⟨eA, hnorm⟩
  let c := numberFieldMixedVectorContinuousLinearEquiv K n
  let e := c.trans eA
  rcases exists_numberFieldInteger_minimalPrimitiveVector_linearEquiv_detOneFirstCol
      K n hn e with ⟨a, β, haPrimitive, hamin, hβdet, hβcol⟩
  refine ⟨a, β, haPrimitive, ?_, hβdet, hβcol⟩
  intro b hbPrimitive
  have hamin' := hamin b hbPrimitive
  calc
    c (numberFieldIntegerVectorEmbedding K a) ⬝ᵥ
        A.mulVec (c (numberFieldIntegerVectorEmbedding K a)) =
        ‖e (numberFieldIntegerVectorEmbedding K a)‖ ^ 2 := by
          simpa [e] using (hnorm (c (numberFieldIntegerVectorEmbedding K a))).symm
    _ ≤ ‖e (numberFieldIntegerVectorEmbedding K b)‖ ^ 2 := by
      gcongr
    _ = c (numberFieldIntegerVectorEmbedding K b) ⬝ᵥ
        A.mulVec (c (numberFieldIntegerVectorEmbedding K b)) := by
          simpa [e] using hnorm (c (numberFieldIntegerVectorEmbedding K b))

end

end GaloisForLFunctions.HTGeometry
