import GaloisForLFunctions.HTGeometry.ABHN.PlaceDiagonalEquiv

/-!
# Hasse detection for polynomial evaluation

The diagonal embeddings into all completions are injective.  Consequently, a polynomial evaluated
at a specified global element vanishes if and only if every completed local evaluation vanishes.
This is a local--global detection theorem for global candidates; it does not claim that arbitrary
independently chosen local roots glue to a global root.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- A polynomial value at a global number-field element vanishes exactly when every local
evaluation at its image in a completion vanishes. -/
theorem numberFieldPolynomial_eval_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) (x : K) :
    p.eval x = 0 ↔ ∀ v : NumberFieldPlace K,
      (p.map (placeEmbedding K v)).eval (placeEmbedding K v x) = 0 := by
  constructor
  · intro h v
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, h, map_zero]
  · intro h
    apply (placeEmbedding K (witnessPlace K)).injective
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact h (witnessPlace K)

/-- A polynomial value at a global rational function vanishes exactly when every local
evaluation at its image in a completion vanishes. -/
theorem rationalFunctionPolynomial_eval_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) (x : RatFunc F) :
    p.eval x = 0 ↔ ∀ v : RationalFunctionPlace F,
      (p.map (rationalFunctionPlaceEmbedding F v)).eval
        (rationalFunctionPlaceEmbedding F v x) = 0 := by
  constructor
  · intro h v
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, h, map_zero]
  · intro h
    apply (rationalFunctionPlaceEmbedding F .infinite).injective
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact h .infinite

/-- Vanishing of a polynomial at a fixed number-field element can be certified at one completion. -/
theorem numberFieldPolynomial_eval_eq_zero_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) (x : K) :
    p.eval x = 0 ↔ ∃ v : NumberFieldPlace K,
      (p.map (placeEmbedding K v)).eval (placeEmbedding K v x) = 0 := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldPolynomial_eval_eq_zero_iff_forall_place K p x).mp h (witnessPlace K)⟩
  · rintro ⟨v, hv⟩
    apply (placeEmbedding K v).injective
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hv

/-- Vanishing of a polynomial at a fixed rational function can be certified at one completion. -/
theorem rationalFunctionPolynomial_eval_eq_zero_iff_exists_place
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) (x : RatFunc F) :
    p.eval x = 0 ↔ ∃ v : RationalFunctionPlace F,
      (p.map (rationalFunctionPlaceEmbedding F v)).eval
        (rationalFunctionPlaceEmbedding F v x) = 0 := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionPolynomial_eval_eq_zero_iff_forall_place F p x).mp h .infinite⟩
  · rintro ⟨v, hv⟩
    apply (rationalFunctionPlaceEmbedding F v).injective
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hv

end GaloisForLFunctions.HTGeometry.ABHN
