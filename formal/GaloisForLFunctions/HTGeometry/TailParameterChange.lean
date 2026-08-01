import GaloisForLFunctions.HTGeometry.TailCoefficientTower

/-!
# The triangular parameter change

Collecting the pieces: over constants containing a primitive `n`-th root of unity, the tail
coefficients are algebraically independent, they generate the fixed field of the scalings
`p i ↦ ζ ^ i * p i`, the field of rational functions in the parameters is generated over them by the
first parameter alone, and its degree there is exactly `n`, the first parameter being an `n`-th root
of the first tail coefficient.

That is the whole of the parameter change: the coefficient field is a rational function field, and
the parameter field is a Kummer extension of it of degree `n`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

open scoped IntermediateField

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
theorem finite_deckGroup [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Finite (deckGroup K n) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_deckGroup hζ]
  exact NeZero.ne n

omit [CharZero K] in
theorem card_deckGroup_fintype [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    [Fintype (deckGroup K n)] : Fintype.card (deckGroup K n) = n := by
  rw [← Nat.card_eq_fintype_card]
  exact card_deckGroup hζ

/-- **The coefficient field is the fixed field of the scalings.** -/
theorem tailCoeffField_eq_deckFixedField_of_primitiveRoot (hn : 0 < n) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : tailCoeffField K n = deckFixedField K n := by
  haveI : NeZero n := ⟨by omega⟩
  haveI := finite_deckGroup (K := K) (n := n) hζ
  haveI : Fintype (deckGroup K n) := Fintype.ofFinite _
  exact tailCoeffField_eq_deckFixedField hn (card_deckGroup_fintype hζ)

/-- **The parameter field has degree exactly `n` over the coefficient field.** -/
theorem finrank_tailCoeffField_of_primitiveRoot (hn : 0 < n) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank (tailCoeffField K n) (FractionRing (MvPolynomial (Fin n) K)) = n := by
  haveI : NeZero n := ⟨by omega⟩
  haveI := finite_deckGroup (K := K) (n := n) hζ
  haveI : Fintype (deckGroup K n) := Fintype.ofFinite _
  exact finrank_tailCoeffField hn (card_deckGroup_fintype hζ)

/-- **The triangular parameter change.**  The tail coefficients are algebraically independent, the
parameter field is generated over them by the first parameter, that parameter is an `n`-th root of
the first tail coefficient, and the degree is exactly `n`. -/
theorem tailParameterChange (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    AlgebraicIndependent K (tailCoeff K n) ∧
      (tailCoeffField K n)⟮algebraMap (MvPolynomial (Fin n) K)
          (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.X (⟨0, hn⟩ : Fin n))⟯ = ⊤ ∧
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
          (MvPolynomial.X (⟨0, hn⟩ : Fin n))) ^ n =
        algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
          (tailCoeff K n (⟨0, hn⟩ : Fin n)) ∧
      Module.finrank (tailCoeffField K n) (FractionRing (MvPolynomial (Fin n) K)) = n :=
  ⟨algebraicIndependent_tailCoeff, tailCoeffField_adjoin_eq_top hn, pow_algebraMap_X_zero hn,
    finrank_tailCoeffField_of_primitiveRoot hn hζ⟩

end GaloisForLFunctions.HTGeometry
