import GaloisForLFunctions.HTGeometry.FacetRestrictionEmbedding
import Mathlib.RingTheory.Localization.Integer

/-!
# Localization after quotienting

Quotienting a localization by the extension of an ideal is the localization of the original
quotient at the image denominator monoid.  Consequently every finite family in the localized
quotient admits a single common denominator and polynomial-quotient numerators.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The canonical map from a quotient into the quotient of a localization. -/
def localizationQuotientMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : R ⧸ I →+* S ⧸ Ideal.map (algebraMap R S) I :=
  Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S)
    Ideal.le_comap_map

/-- The quotient of a localization is the localization of the corresponding quotient. -/
theorem isLocalization_localizationQuotientMap
    {R S : Type*} [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S]
    (I : Ideal R) :
    letI := (localizationQuotientMap (S := S) I).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I))
      (S ⧸ Ideal.map (algebraMap R S) I) := by
  letI := (localizationQuotientMap (S := S) I).toAlgebra
  apply IsLocalization.of_surjective M S
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I))
    Ideal.Quotient.mk_surjective
  · ext r
    change Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)
        (algebraMap R S r) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)
        (algebraMap R S r)
    rfl
  · rw [Ideal.mk_ker, Ideal.mk_ker]

/-- Every finite family in a localized quotient has one common denominator. -/
theorem exists_commonDenominator_localizedQuotient
    {R S ι : Type*} [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S]
    (I : Ideal R) [Fintype ι]
    (P : ι → S ⧸ Ideal.map (algebraMap R S) I) :
    letI := (localizationQuotientMap (S := S) I).toAlgebra
    ∃ d : M.map (Ideal.Quotient.mk I), ∀ i,
      IsLocalization.IsInteger (R ⧸ I) ((d : R ⧸ I) • P i) := by
  letI := (localizationQuotientMap (S := S) I).toAlgebra
  letI : IsLocalization (M.map (Ideal.Quotient.mk I))
      (S ⧸ Ideal.map (algebraMap R S) I) :=
    isLocalization_localizationQuotientMap M I
  exact IsLocalization.exist_integer_multiples_of_finite
    (M.map (Ideal.Quotient.mk I)) P

end

end GaloisForLFunctions.HTGeometry
