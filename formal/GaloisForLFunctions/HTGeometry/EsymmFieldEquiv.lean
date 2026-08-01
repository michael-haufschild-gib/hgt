import GaloisForLFunctions.HTGeometry.EsymmRangeField

/-!
# The coefficient field as a rational function field

The model embedding is injective and its image is exactly the coefficient field, so it is an
isomorphism onto it.  Under this isomorphism the top elementary symmetric function corresponds to a
variable.

That is what lets statements proved about a variable of a polynomial ring — primality, and through
it irreducibility of the radical polynomial — be read as statements about the constant coefficient
of the generic polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- **The coefficient field is a rational function field in the coefficients.** -/
noncomputable def esymmFieldEquiv (K : Type*) [Field K] (d : ℕ) :
    FractionRing (MvPolynomial (Fin d) K) ≃+* esymmField K d := by
  refine RingEquiv.ofBijective
    ((esymmFracEmbedding K d).codRestrict (esymmField K d).toSubfield.toSubring ?_) ⟨?_, ?_⟩
  · intro u
    have h : esymmFracEmbedding K d u ∈ esymmRangeField K d := ⟨u, rfl⟩
    rw [esymmRangeField_eq_esymmField] at h
    exact h
  · intro u v huv
    exact esymmFracEmbedding_injective (K := K) (d := d) (congrArg Subtype.val huv)
  · rintro ⟨x, hx⟩
    rw [← esymmRangeField_eq_esymmField] at hx
    obtain ⟨u, hu⟩ := hx
    exact ⟨u, Subtype.ext hu⟩

theorem esymmFieldEquiv_apply (u : FractionRing (MvPolynomial (Fin d) K)) :
    ((esymmFieldEquiv K d u : esymmField K d) : SymmetricRationalField K d) =
      esymmFracEmbedding K d u := rfl

theorem esymmFieldEquiv_X (i : Fin d) :
    ((esymmFieldEquiv K d
        (algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))
          (MvPolynomial.X i)) : esymmField K d) : SymmetricRationalField K d) =
      esymmGen K d i := by
  rw [esymmFieldEquiv_apply, esymmFracEmbedding_algebraMap, esymmEmbedding, MvPolynomial.aeval_X]

end GaloisForLFunctions.HTGeometry
