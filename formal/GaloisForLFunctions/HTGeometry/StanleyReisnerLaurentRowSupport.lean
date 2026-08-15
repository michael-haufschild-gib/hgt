import GaloisForLFunctions.HTGeometry.LocalizedStanleyReisnerMatroidRank

/-!
# The Laurent row of a facet is supported on that facet

A facet translation coordinate is a polynomial in the variables of its own facet, and the common
denominator shift only subtracts an exponent visible on that facet.  So every Laurent exponent
vector occurring in the row of a facet vanishes outside that facet, and the finite coordinate packet
of a Stanley--Reisner Laurent family indexes translations supported on their own facet.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open scoped Classical

noncomputable section

variable {R α ι : Type*} [CommRing R] [DecidableEq α]

/-- A facet translation polynomial uses only the variables of its facet. -/
theorem support_facetTranslationPolynomialEmbedding_eq_zero
    (F : Finset α) (Q : MvPolynomial F R) {e : α →₀ ℕ}
    (he : e ∈ (facetTranslationPolynomialEmbedding (R := R) F Q).support)
    {v : α} (hv : v ∉ F) : e v = 0 := by
  have hren : facetTranslationPolynomialEmbedding (R := R) F Q
      = MvPolynomial.rename (facetVariableInclusion (R := R) F)
        (differenceToTranslationHom Q) := rfl
  rw [hren, MvPolynomial.support_rename_of_injective
    (facetVariableInclusion_injective (R := R) F)] at he
  obtain ⟨e', -, rfl⟩ := Finset.mem_image.mp he
  refine Finsupp.mapDomain_notin_range e' v ?_
  rintro ⟨u, rfl⟩
  exact hv u.2

/-- The facet coordinate of a Stanley--Reisner class uses only the variables of its facet. -/
theorem support_stanleyReisnerFacetTranslationCoordinates_eq_zero
    (facets : Finset (Finset α)) (P : MvPolynomial α R ⧸ stanleyReisnerIdeal R facets)
    (F : facets) {e : α →₀ ℕ}
    (he : e ∈ (stanleyReisnerFacetTranslationCoordinates facets P F).support)
    {v : α} (hv : v ∉ F.1) : e v = 0 := by
  have hcoord : stanleyReisnerFacetTranslationCoordinates facets P F
      = facetTranslationPolynomialEmbedding (R := R) F.1
        (stanleyReisnerFacetPolynomialCoordinates facets P F) := rfl
  rw [hcoord] at he
  exact support_facetTranslationPolynomialEmbedding_eq_zero F.1 _ he hv

variable [Fintype α]

/-- Every Laurent exponent of the row of a facet vanishes outside that facet. -/
theorem stanleyReisnerLaurentRows_support_eq_zero
    (d : translationSubmonoid R α) (facets : Finset (Finset α))
    (N : ι → MvPolynomial α R ⧸ stanleyReisnerIdeal R facets)
    (i : ι) (F : facets) {g : α → ℤ}
    (hg : g ∈ (stanleyReisnerLaurentRows d facets N i F).support)
    {v : α} (hv : v ∉ F.1) : g v = 0 := by
  have hrow : stanleyReisnerLaurentRows d facets N i F
      = facetLaurentShift d F.1 (stanleyReisnerFacetTranslationCoordinates facets (N i) F) := rfl
  rw [hrow, facetLaurentShift] at hg
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
  have hzero : e v = 0 :=
    support_stanleyReisnerFacetTranslationCoordinates_eq_zero facets (N i) F he hv
  rw [facetLaurentExponentShift, if_neg hv, hzero]
  simp

/-- The finite coordinate packet of a Stanley--Reisner Laurent family indexes translations
supported on their own facet. -/
theorem finiteFinsuppRowIndex_stanleyReisnerLaurentRows_eq_zero
    [Fintype ι]
    (d : translationSubmonoid R α) (facets : Finset (Finset α))
    (N : ι → MvPolynomial α R ⧸ stanleyReisnerIdeal R facets)
    (q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N))
    {v : α} (hv : v ∉ (q.1.1 : Finset α)) : q.1.2 v = 0 := by
  obtain ⟨⟨F, g⟩, hq⟩ := q
  simp only [finiteFinsuppRowSupport, Finset.mem_biUnion, Finset.mem_univ, true_and] at hq
  obtain ⟨i, F', hF'⟩ := hq
  obtain ⟨g', hg', hpair⟩ := Finset.mem_image.mp hF'
  rw [Prod.mk.injEq] at hpair
  obtain ⟨hFF, hgg⟩ := hpair
  subst hFF
  subst hgg
  exact stanleyReisnerLaurentRows_support_eq_zero d facets N i F' hg' hv

end

end GaloisForLFunctions.HTGeometry
