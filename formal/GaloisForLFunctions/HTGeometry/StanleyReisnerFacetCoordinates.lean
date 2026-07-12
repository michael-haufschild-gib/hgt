import GaloisForLFunctions.HTGeometry.FacetRestrictionEmbedding
import GaloisForLFunctions.HTGeometry.FacetPolynomialQuotient

/-!
# Stanley--Reisner facet polynomial coordinates

The global Stanley--Reisner quotient embeds faithfully into the product of polynomial rings on its
facets.  This is the numerator-coordinate form of the facet sewing: every global class is detected
by its complete family of ordinary finite facet polynomials.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Complete polynomial facet coordinates of a Stanley--Reisner quotient class. -/
def stanleyReisnerFacetPolynomialCoordinates
    {R α : Type*} [CommRing R] [DecidableEq α]
    (facets : Finset (Finset α)) :
    (MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) →ₐ[R]
      ((F : facets) → MvPolynomial F.1 R) := by
  let hI : stanleyReisnerIdeal R facets =
      ⨅ F : facets, facetIdeal R F.1 := by
    rw [stanleyReisnerIdeal_eq_inf_facetIdeal]
    apply le_antisymm
    · apply le_iInf
      intro F
      exact Finset.inf_le_of_le F.2 le_rfl
    · apply Finset.le_inf
      intro F hF
      exact iInf_le_of_le ⟨F, hF⟩ le_rfl
  let e := quotientFacetEmbedding (k := R)
    (stanleyReisnerIdeal R facets)
    (fun F : facets => facetIdeal R F.1) hI
  exact
    { toFun := fun P F => facetPolynomialQuotientEquiv F.1 (e P F)
      map_one' := by funext F; simp
      map_mul' P Q := by funext F; simp
      map_zero' := by funext F; simp
      map_add' P Q := by funext F; simp
      commutes' r := by funext F; simp }

/-- Complete facet polynomial coordinates detect every global Stanley--Reisner class. -/
theorem stanleyReisnerFacetPolynomialCoordinates_injective
    {R α : Type*} [CommRing R] [DecidableEq α]
    (facets : Finset (Finset α)) :
    Function.Injective (stanleyReisnerFacetPolynomialCoordinates (R := R) facets) := by
  intro P Q h
  let hI : stanleyReisnerIdeal R facets =
      ⨅ F : facets, facetIdeal R F.1 := by
    rw [stanleyReisnerIdeal_eq_inf_facetIdeal]
    apply le_antisymm
    · apply le_iInf
      intro F
      exact Finset.inf_le_of_le F.2 le_rfl
    · apply Finset.le_inf
      intro F hF
      exact iInf_le_of_le ⟨F, hF⟩ le_rfl
  apply quotientFacetEmbedding_injective (k := R)
    (stanleyReisnerIdeal R facets)
    (fun F : facets => facetIdeal R F.1) hI
  funext F
  apply (facetPolynomialQuotientEquiv F.1).injective
  exact congrFun h F

end

end GaloisForLFunctions.HTGeometry
