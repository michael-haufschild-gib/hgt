import GaloisForLFunctions.HTGeometry.StanleyReisnerNumeratorDifferentialMatroid
import GaloisForLFunctions.HTGeometry.TranslationDenominatorLaurentShift

/-!
# Stanley--Reisner Laurent rows

A common translation denominator shifts every facet numerator support by one fixed negative
integral exponent vector.  This shift is an injective linear reindexing, so the resulting finite
Laurent coefficient rows have exactly the same linear matroid as the numerator classes in the
Stanley--Reisner quotient.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Laurent denominator shifting as a linear map on one facet row. -/
def facetLaurentShiftLinearMap
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (F : Finset α) :
    MvPolynomial α R →ₗ[R] ((α → ℤ) →₀ R) :=
  Finsupp.lmapDomain R R (facetLaurentExponentShift d F)

/-- The linear-map implementation agrees with coefficient reindexing. -/
theorem facetLaurentShiftLinearMap_apply
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (F : Finset α)
    (P : MvPolynomial α R) :
    facetLaurentShiftLinearMap d F P = facetLaurentShift d F P := rfl

/-- One-facet Laurent shifting is injective. -/
theorem facetLaurentShiftLinearMap_injective
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (F : Finset α) :
    Function.Injective (facetLaurentShiftLinearMap d F) :=
  facetLaurentShift_injective d F

/-- Apply the same global denominator with its facet-visible exponent on every facet row. -/
def allFacetLaurentShiftLinearMap
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α)) :
    ((F : facets) → MvPolynomial α R) →ₗ[R]
      ((F : facets) → (α → ℤ) →₀ R) where
  toFun Q F := facetLaurentShiftLinearMap d F.1 (Q F)
  map_add' P Q := by funext F; simp
  map_smul' r P := by funext F; simp

/-- Simultaneous Laurent shifting of all facets is injective. -/
theorem allFacetLaurentShiftLinearMap_injective
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α)) :
    Function.Injective (allFacetLaurentShiftLinearMap d facets) := by
  intro P Q h
  funext F
  apply facetLaurentShiftLinearMap_injective d F.1
  exact congrFun h F

/-- A common Laurent denominator preserves and reflects row independence. -/
theorem linearIndependent_allFacetLaurentShift_iff
    {R α ι : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α))
    (Q : ι → (F : facets) → MvPolynomial α R) :
    LinearIndependent R ((allFacetLaurentShiftLinearMap d facets) ∘ Q) ↔
      LinearIndependent R Q := by
  let f := allFacetLaurentShiftLinearMap d facets
  have hf : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr
    (allFacetLaurentShiftLinearMap_injective d facets)
  constructor
  · intro h
    exact h.of_comp f
  · intro h
    exact h.map' f hf

/-- Finite Laurent rows attached to Stanley--Reisner numerator classes and a common denominator. -/
def stanleyReisnerLaurentRows
    {R α ι : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α))
    (N : ι → MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) :
    ι → (F : facets) → (α → ℤ) →₀ R :=
  (allFacetLaurentShiftLinearMap d facets) ∘
    (stanleyReisnerFacetTranslationCoordinates facets) ∘ N

/-- **Localized Stanley--Reisner row law.**  The Laurent coefficient rows obtained after common
denominator clearing are linearly independent exactly when the numerator quotient classes are. -/
theorem linearIndependent_stanleyReisnerLaurentRows_iff
    {R α ι : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α))
    (N : ι → MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) :
    LinearIndependent R (stanleyReisnerLaurentRows d facets N) ↔
      LinearIndependent R N := by
  rw [stanleyReisnerLaurentRows,
    linearIndependent_allFacetLaurentShift_iff]
  exact linearIndependent_stanleyReisnerFacetTranslationCoordinates_iff facets N

end

end GaloisForLFunctions.HTGeometry
