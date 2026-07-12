import GaloisForLFunctions.HTGeometry.DifferenceTranslationCoordinates
import GaloisForLFunctions.HTGeometry.FiniteFinsuppOperatorRows

/-!
# Facet translation coordinates

Complete Stanley--Reisner facet polynomials are converted from difference coordinates
`x_v = t_v - 1` to finite translation coordinates and embedded back into the common vertex
polynomial ring.  The resulting nested finitely supported coefficient rows faithfully encode the
global quotient and preserve and reflect every linear circuit over the coefficient ring.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Convert a facet polynomial to translation coordinates and embed its variables globally. -/
def facetTranslationPolynomialEmbedding
    {R α : Type*} [CommRing R] (F : Finset α) :
    MvPolynomial F R →ₐ[R] MvPolynomial α R :=
  (MvPolynomial.rename (facetVariableInclusion (R := R) F)).comp
    differenceToTranslationHom

/-- Facet translation-coordinate expansion is injective. -/
theorem facetTranslationPolynomialEmbedding_injective
    {R α : Type*} [CommRing R] (F : Finset α) :
    Function.Injective (facetTranslationPolynomialEmbedding (R := R) F) :=
  (MvPolynomial.rename_injective _
    (facetVariableInclusion_injective (R := R) F)).comp
      (differenceTranslationEquiv (R := R) (α := F)).injective

/-- Complete finite translation-coordinate rows of a Stanley--Reisner quotient class. -/
def stanleyReisnerFacetTranslationCoordinates
    {R α : Type*} [CommRing R] [DecidableEq α]
    (facets : Finset (Finset α)) :
    (MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) →ₐ[R]
      ((F : facets) → MvPolynomial α R) := by
  exact
    { toFun := fun P F => facetTranslationPolynomialEmbedding F.1
          (stanleyReisnerFacetPolynomialCoordinates facets P F)
      map_one' := by funext F; simp [facetTranslationPolynomialEmbedding]
      map_mul' P Q := by funext F; simp [facetTranslationPolynomialEmbedding]
      map_zero' := by funext F; simp [facetTranslationPolynomialEmbedding]
      map_add' P Q := by funext F; simp [facetTranslationPolynomialEmbedding]
      commutes' r := by funext F; simp [facetTranslationPolynomialEmbedding] }

/-- Complete facet translation coordinates detect every global quotient class. -/
theorem stanleyReisnerFacetTranslationCoordinates_injective
    {R α : Type*} [CommRing R] [DecidableEq α]
    (facets : Finset (Finset α)) :
    Function.Injective (stanleyReisnerFacetTranslationCoordinates (R := R) facets) := by
  intro P Q h
  apply stanleyReisnerFacetPolynomialCoordinates_injective (R := R) facets
  funext F
  apply facetTranslationPolynomialEmbedding_injective (R := R) F.1
  exact congrFun h F

/-- **Facet translation-row law.**  A family of global Stanley--Reisner classes is linearly
independent exactly when its complete finite facet translation-coordinate rows are. -/
theorem linearIndependent_stanleyReisnerFacetTranslationCoordinates_iff
    {R α ι : Type*} [CommRing R] [DecidableEq α]
    (facets : Finset (Finset α))
    (P : ι → MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) :
    LinearIndependent R
        ((stanleyReisnerFacetTranslationCoordinates (R := R) facets) ∘ P) ↔
      LinearIndependent R P := by
  let f := (stanleyReisnerFacetTranslationCoordinates (R := R) facets).toLinearMap
  have hf : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr
    (stanleyReisnerFacetTranslationCoordinates_injective (R := R) facets)
  constructor
  · intro h
    exact h.of_comp f
  · intro h
    exact h.map' f hf

end

end GaloisForLFunctions.HTGeometry
