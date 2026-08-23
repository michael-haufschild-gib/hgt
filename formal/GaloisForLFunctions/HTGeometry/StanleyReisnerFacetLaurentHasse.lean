import GaloisForLFunctions.HTGeometry.StanleyReisnerLaurentRows

/-!
# Hasse detection by all Stanley--Reisner facet Laurent charts

Complete facet translation coordinates detect a global Stanley--Reisner quotient class.  Applying
a common Laurent denominator shift in every facet preserves that detection, so the complete family
of Laurent coefficient charts remains conservative.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Send a global Stanley--Reisner class to all of its denominator-shifted facet Laurent rows. -/
def stanleyReisnerFacetLaurentHasseMap
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α)) :
    (MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) →ₗ[R]
      ((F : facets) → (α → ℤ) →₀ R) :=
  (allFacetLaurentShiftLinearMap d facets).comp
    (stanleyReisnerFacetTranslationCoordinates facets).toLinearMap

/-- The complete family of denominator-shifted facet Laurent rows loses no global quotient
class. -/
theorem stanleyReisnerFacetLaurentHasseMap_injective
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α)) :
    Function.Injective (stanleyReisnerFacetLaurentHasseMap d facets) := by
  intro x y h
  apply stanleyReisnerFacetTranslationCoordinates_injective (R := R) facets
  apply allFacetLaurentShiftLinearMap_injective d facets
  exact h

/-- Two global Stanley--Reisner classes agree exactly when all combined facet Laurent rows agree. -/
theorem stanleyReisnerFacetLaurent_congr_hasse_iff
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α))
    (x y : MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) :
    stanleyReisnerFacetLaurentHasseMap d facets x =
      stanleyReisnerFacetLaurentHasseMap d facets y ↔ x = y := by
  constructor
  · intro h
    exact stanleyReisnerFacetLaurentHasseMap_injective d facets h
  · exact congrArg _

/-- Pointwise agreement on every denominator-shifted facet Laurent chart detects equality of the
global quotient classes. -/
theorem stanleyReisnerFacetLaurent_pointwise_congr_hasse_iff
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α))
    (x y : MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) :
    (∀ F : facets,
      facetLaurentShift d F.1
          (stanleyReisnerFacetTranslationCoordinates facets x F) =
        facetLaurentShift d F.1
          (stanleyReisnerFacetTranslationCoordinates facets y F)) ↔ x = y := by
  rw [← stanleyReisnerFacetLaurent_congr_hasse_iff d facets x y]
  exact ⟨fun h => funext h, fun h F => congrFun h F⟩

end


end GaloisForLFunctions.HTGeometry
