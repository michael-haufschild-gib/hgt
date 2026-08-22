import GaloisForLFunctions.HTGeometry.ABHN.HasseMvPolynomialEvaluation

/-!
# Hasse detection for polynomial identities

The diagonal maps into all completions are injective on polynomial coefficients. Consequently, a
global polynomial relation is zero exactly when each of its completed coefficient extensions is
zero. This is relation-level local--global detection, complementary to pointwise evaluation.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-- A polynomial over a number field is zero exactly when every completed coefficient extension
is zero. -/
theorem numberFieldPolynomial_map_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) :
    p = 0 ↔ ∀ v : NumberFieldPlace K, p.map (placeEmbedding K v) = 0 := by
  constructor
  · intro h v
    rw [h, Polynomial.map_zero]
  · intro h
    apply Polynomial.map_injective (placeEmbedding K (witnessPlace K))
      (placeEmbedding K (witnessPlace K)).injective
    simpa using h (witnessPlace K)

/-- A multivariable polynomial over a number field is zero exactly when every completed
coefficient extension is zero. -/
theorem numberFieldMvPolynomial_map_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {σ : Type w} (p : MvPolynomial σ K) :
    p = 0 ↔ ∀ v : NumberFieldPlace K, MvPolynomial.map (placeEmbedding K v) p = 0 := by
  constructor
  · intro h v
    rw [h, map_zero]
  · intro h
    apply MvPolynomial.map_injective (placeEmbedding K (witnessPlace K))
      (placeEmbedding K (witnessPlace K)).injective
    simpa using h (witnessPlace K)

/-- A polynomial over `F(t)` is zero exactly when every completed coefficient extension is zero. -/
theorem rationalFunctionPolynomial_map_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) :
    p = 0 ↔ ∀ v : RationalFunctionPlace F, p.map (rationalFunctionPlaceEmbedding F v) = 0 := by
  constructor
  · intro h v
    rw [h, Polynomial.map_zero]
  · intro h
    apply Polynomial.map_injective (rationalFunctionPlaceEmbedding F .infinite)
      (rationalFunctionPlaceEmbedding F .infinite).injective
    simpa using h .infinite

/-- A multivariable polynomial over `F(t)` is zero exactly when every completed coefficient
extension is zero. -/
theorem rationalFunctionMvPolynomial_map_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] {σ : Type w} (p : MvPolynomial σ (RatFunc F)) :
    p = 0 ↔ ∀ v : RationalFunctionPlace F,
      MvPolynomial.map (rationalFunctionPlaceEmbedding F v) p = 0 := by
  constructor
  · intro h v
    rw [h, map_zero]
  · intro h
    apply MvPolynomial.map_injective (rationalFunctionPlaceEmbedding F .infinite)
      (rationalFunctionPlaceEmbedding F .infinite).injective
    simpa using h .infinite

/-- A number-field polynomial identity can be certified at one completion. -/
theorem numberFieldPolynomial_map_eq_zero_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) :
    p = 0 ↔ ∃ v : NumberFieldPlace K, p.map (placeEmbedding K v) = 0 := by
  constructor
  · intro h
    exact ⟨witnessPlace K, by rw [h, Polynomial.map_zero]⟩
  · rintro ⟨v, hv⟩
    apply Polynomial.map_injective (placeEmbedding K v) (placeEmbedding K v).injective
    simpa using hv

/-- A number-field multivariable polynomial identity can be certified at one completion. -/
theorem numberFieldMvPolynomial_map_eq_zero_iff_exists_place
    (K : Type u) [Field K] [NumberField K] {σ : Type w} (p : MvPolynomial σ K) :
    p = 0 ↔ ∃ v : NumberFieldPlace K, MvPolynomial.map (placeEmbedding K v) p = 0 := by
  constructor
  · intro h
    exact ⟨witnessPlace K, by rw [h, map_zero]⟩
  · rintro ⟨v, hv⟩
    apply MvPolynomial.map_injective (placeEmbedding K v) (placeEmbedding K v).injective
    simpa using hv

/-- An `F(t)`-polynomial identity can be certified at one completion. -/
theorem rationalFunctionPolynomial_map_eq_zero_iff_exists_place
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) :
    p = 0 ↔ ∃ v : RationalFunctionPlace F, p.map (rationalFunctionPlaceEmbedding F v) = 0 := by
  constructor
  · intro h
    exact ⟨.infinite, by rw [h, Polynomial.map_zero]⟩
  · rintro ⟨v, hv⟩
    apply Polynomial.map_injective (rationalFunctionPlaceEmbedding F v)
      (rationalFunctionPlaceEmbedding F v).injective
    simpa using hv

/-- An `F(t)`-multivariable polynomial identity can be certified at one completion. -/
theorem rationalFunctionMvPolynomial_map_eq_zero_iff_exists_place
    (F : Type u) [Field F] [Finite F] {σ : Type w} (p : MvPolynomial σ (RatFunc F)) :
    p = 0 ↔ ∃ v : RationalFunctionPlace F,
      MvPolynomial.map (rationalFunctionPlaceEmbedding F v) p = 0 := by
  constructor
  · intro h
    exact ⟨.infinite, by rw [h, map_zero]⟩
  · rintro ⟨v, hv⟩
    apply MvPolynomial.map_injective (rationalFunctionPlaceEmbedding F v)
      (rationalFunctionPlaceEmbedding F v).injective
    simpa using hv

end GaloisForLFunctions.HTGeometry.ABHN
