import GaloisForLFunctions.HTGeometry.StanleyReisnerLaurentRows

/-!
# Facet slices of Stanley--Reisner Laurent rows

A facet coordinate of a Stanley--Reisner class is a polynomial in the variables of that facet
alone.  Embedding it back into the ambient polynomial ring and clearing a common translation
denominator therefore produces Laurent exponents that vanish outside the facet.

Consequently the finite index set of the Laurent operator rows lies in the *facet slice*

```
{(F, m) : m v = 0 for every v ∉ F},
```

which is the exact index set the compressed realization has to separate: a translation attached to
a vertex outside a facet does not move that facet's summand.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- A facet translation-coordinate embedding uses only the variables of its facet. -/
theorem facetTranslationPolynomialEmbedding_support_slice
    {R α : Type*} [CommRing R] [DecidableEq α] (F : Finset α)
    (P : MvPolynomial F R) {e : α →₀ ℕ}
    (he : e ∈ (facetTranslationPolynomialEmbedding (R := R) F P).support)
    {v : α} (hv : v ∉ F) : e v = 0 := by
  classical
  have hrewrite : facetTranslationPolynomialEmbedding (R := R) F P =
      MvPolynomial.rename (facetVariableInclusion (R := R) F)
        (differenceToTranslationHom P) := rfl
  rw [hrewrite, MvPolynomial.support_rename_of_injective
    (facetVariableInclusion_injective (R := R) F)] at he
  obtain ⟨e', -, rfl⟩ := Finset.mem_image.1 he
  refine Finsupp.mapDomain_notin_range e' v ?_
  rintro ⟨w, rfl⟩
  exact hv w.2

/-- Every nonzero Laurent row coefficient of a facet has exponent supported inside that facet. -/
theorem stanleyReisnerLaurentRows_slice
    {R α ι : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α))
    (N : ι → MvPolynomial α R ⧸ stanleyReisnerIdeal R facets)
    (i : ι) (F : facets) {m : α → ℤ}
    (hm : m ∈ (stanleyReisnerLaurentRows d facets N i F).support)
    {v : α} (hv : v ∉ F.1) : m v = 0 := by
  classical
  have hrow : stanleyReisnerLaurentRows d facets N i F =
      Finsupp.mapDomain (facetLaurentExponentShift d F.1)
        (AddMonoidAlgebra.coeff
          (facetTranslationPolynomialEmbedding (R := R) F.1
            (stanleyReisnerFacetPolynomialCoordinates facets (N i) F))) := rfl
  rw [hrow] at hm
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hm)
  have hze : e v = 0 :=
    facetTranslationPolynomialEmbedding_support_slice F.1 _ he hv
  simp [facetLaurentExponentShift, hv, hze]

/-- **Facet slice of the finite row index.**  Every index of the finite Laurent operator rows has
its exponent supported inside its own facet. -/
theorem finiteFinsuppRowIndex_slice
    {R α ι : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq (α → ℤ)]
    (d : translationSubmonoid R α) (facets : Finset (Finset α))
    (N : ι → MvPolynomial α R ⧸ stanleyReisnerIdeal R facets)
    (q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N))
    {v : α} (hv : v ∉ q.1.1.1) : q.1.2 v = 0 := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 q.2
  obtain ⟨F, -, hF⟩ := Finset.mem_biUnion.1 hi
  obtain ⟨g, hg, hgq⟩ := Finset.mem_image.1 hF
  have hFq : F = q.1.1 := congrArg Prod.fst hgq
  have hgq2 : g = q.1.2 := congrArg Prod.snd hgq
  subst hFq
  subst hgq2
  exact stanleyReisnerLaurentRows_slice d facets N i q.1.1 hg hv

end

end GaloisForLFunctions.HTGeometry
