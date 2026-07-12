import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetIdeal

/-!
# Facet restriction embeddings

The quotient by an intersection of ideals embeds in the product of the individual quotients.  This
module makes that elementary fact linear-algebraically exact: a family of global quotient classes
is linearly independent if and only if its complete facet-restriction family is.  The final
specialization applies the localized Stanley--Reisner facet decomposition.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Simultaneously reduce an element modulo every ideal in a family. -/
def facetQuotientMap
    {k A σ : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (J : σ → Ideal A) : A →ₐ[k] ((s : σ) → A ⧸ J s) where
  toFun a s := Ideal.Quotient.mk (J s) a
  map_one' := by funext s; simp
  map_mul' a b := by funext s; simp
  map_zero' := by funext s; simp
  map_add' a b := by funext s; simp
  commutes' r := by funext s; simp

/-- The simultaneous quotient map kills exactly the elements lying in every ideal. -/
theorem mem_ker_facetQuotientMap_iff
    {k A σ : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (J : σ → Ideal A) (a : A) :
    a ∈ RingHom.ker (facetQuotientMap (k := k) J).toRingHom ↔ ∀ s, a ∈ J s := by
  rw [RingHom.mem_ker]
  constructor
  · intro h s
    have hs := congrFun h s
    exact Ideal.Quotient.eq_zero_iff_mem.mp hs
  · intro h
    funext s
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h s)

/-- The kernel of simultaneous facet restriction is the intersection of the facet ideals. -/
theorem ker_facetQuotientMap
    {k A σ : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (J : σ → Ideal A) :
    RingHom.ker (facetQuotientMap (k := k) J).toRingHom = ⨅ s, J s := by
  ext a
  rw [mem_ker_facetQuotientMap_iff, Ideal.mem_iInf]

/-- The canonical map from the quotient by the intersection to the product of quotients. -/
def facetQuotientEmbedding
    {k A σ : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (J : σ → Ideal A) :
    A ⧸ (⨅ s, J s) →ₐ[k] ((s : σ) → A ⧸ J s) :=
  Ideal.Quotient.liftₐ (⨅ s, J s) (facetQuotientMap (k := k) J) (by
    intro a ha
    apply funext
    intro s
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_iInf.mp ha s))

/-- The canonical intersection-quotient map is injective. -/
theorem facetQuotientEmbedding_injective
    {k A σ : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (J : σ → Ideal A) :
    Function.Injective (facetQuotientEmbedding (k := k) J) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_iInf.mpr
  intro s
  have hs := congrFun hab s
  change Ideal.Quotient.mk (J s) a = Ideal.Quotient.mk (J s) b at hs
  rw [Ideal.Quotient.eq] at hs
  exact hs

/-- Simultaneous facet restriction preserves and reflects linear independence. -/
theorem linearIndependent_facetQuotientEmbedding_iff
    {k A σ ι : Type*} [Field k] [CommRing A] [Algebra k A]
    (J : σ → Ideal A) (P : ι → A ⧸ (⨅ s, J s)) :
    LinearIndependent k ((facetQuotientEmbedding (k := k) J) ∘ P) ↔
      LinearIndependent k P := by
  constructor
  · intro h
    exact h.of_comp (facetQuotientEmbedding (k := k) J).toLinearMap
  · intro h
    exact h.map' (facetQuotientEmbedding (k := k) J).toLinearMap
      (LinearMap.ker_eq_bot.mpr (facetQuotientEmbedding_injective (k := k) J))

/-- The facet embedding written for any ideal identified with the facet-ideal intersection. -/
def quotientFacetEmbedding
    {k A σ : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (I : Ideal A) (J : σ → Ideal A) (hI : I = ⨅ s, J s) :
    A ⧸ I →ₐ[k] ((s : σ) → A ⧸ J s) := by
  subst I
  exact facetQuotientEmbedding (k := k) J

/-- An identified intersection quotient embeds in the product of its facet quotients. -/
theorem quotientFacetEmbedding_injective
    {k A σ : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (I : Ideal A) (J : σ → Ideal A) (hI : I = ⨅ s, J s) :
    Function.Injective (quotientFacetEmbedding (k := k) I J hI) := by
  subst I
  exact facetQuotientEmbedding_injective (k := k) J

/-- The identified intersection embedding preserves and reflects linear independence. -/
theorem linearIndependent_quotientFacetEmbedding_iff
    {k A σ ι : Type*} [Field k] [CommRing A] [Algebra k A]
    (I : Ideal A) (J : σ → Ideal A) (hI : I = ⨅ s, J s)
    (P : ι → A ⧸ I) :
    LinearIndependent k ((quotientFacetEmbedding (k := k) I J hI) ∘ P) ↔
      LinearIndependent k P := by
  subst I
  exact linearIndependent_facetQuotientEmbedding_iff J P

/-- The extension of a Stanley--Reisner ideal to a localization. -/
def localizedStanleyReisnerIdeal
    {R α S : Type*} [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) : Ideal S :=
  Ideal.map (algebraMap (MvPolynomial α R) S) (stanleyReisnerIdeal R facets)

/-- The extension of a coordinate facet ideal to a localization. -/
def localizedFacetIdeal
    {R α S : Type*} [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (F : Finset α) : Ideal S :=
  Ideal.map (algebraMap (MvPolynomial α R) S) (facetIdeal R F)

/-- The localized Stanley--Reisner ideal is the intersection indexed by its actual facets. -/
theorem localizedStanleyReisnerIdeal_eq_iInf_localizedFacetIdeal
    {R α S : Type*} [CommRing R] [CommRing S] [DecidableEq α]
    (M : Submonoid (MvPolynomial α R))
    [Algebra (MvPolynomial α R) S] [IsLocalization M S]
    (facets : Finset (Finset α)) :
    localizedStanleyReisnerIdeal (R := R) (S := S) facets =
      ⨅ F : facets, localizedFacetIdeal (R := R) (S := S) F.1 := by
  change Ideal.map (algebraMap (MvPolynomial α R) S)
      (stanleyReisnerIdeal R facets) =
    ⨅ F : facets, Ideal.map (algebraMap (MvPolynomial α R) S)
      (facetIdeal R F.1)
  rw [localized_stanleyReisnerIdeal_eq_inf_facetIdeal M facets]
  apply le_antisymm
  · apply le_iInf
    intro F
    exact Finset.inf_le_of_le F.2 le_rfl
  · apply Finset.le_inf
    intro F hF
    exact iInf_le_of_le ⟨F, hF⟩ le_rfl

/-- The localized Stanley--Reisner quotient embedded in the product of its facet quotients. -/
def localizedStanleyReisnerFacetEmbedding
    {k R α S : Type*} [CommRing k] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra k S] (M : Submonoid (MvPolynomial α R))
    [Algebra (MvPolynomial α R) S] [IsLocalization M S]
    (facets : Finset (Finset α)) :
    S ⧸ localizedStanleyReisnerIdeal (R := R) (S := S) facets →ₐ[k]
      ((F : facets) → S ⧸ localizedFacetIdeal (R := R) (S := S) F.1) :=
  quotientFacetEmbedding (k := k)
    (localizedStanleyReisnerIdeal (R := R) (S := S) facets)
    (fun F : facets => localizedFacetIdeal (R := R) (S := S) F.1)
    (localizedStanleyReisnerIdeal_eq_iInf_localizedFacetIdeal M facets)

/-- The complete localized facet-restriction map is injective. -/
theorem localizedStanleyReisnerFacetEmbedding_injective
    {k R α S : Type*} [CommRing k] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra k S] (M : Submonoid (MvPolynomial α R))
    [Algebra (MvPolynomial α R) S] [IsLocalization M S]
    (facets : Finset (Finset α)) :
    Function.Injective (localizedStanleyReisnerFacetEmbedding
      (k := k) (R := R) (S := S) M facets) :=
  quotientFacetEmbedding_injective (k := k)
    (localizedStanleyReisnerIdeal (S := S) facets)
    (fun F : facets => localizedFacetIdeal (R := R) (S := S) F.1)
    (localizedStanleyReisnerIdeal_eq_iInf_localizedFacetIdeal M facets)

/-- **Localized facet-span law.**  Global classes in a localized Stanley--Reisner quotient are
linearly independent exactly when their complete facet restrictions are linearly independent. -/
theorem linearIndependent_localizedStanleyReisnerFacetEmbedding_iff
    {k R α S ι : Type*} [Field k] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra k S] (M : Submonoid (MvPolynomial α R))
    [Algebra (MvPolynomial α R) S] [IsLocalization M S]
    (facets : Finset (Finset α))
    (P : ι → S ⧸ localizedStanleyReisnerIdeal (R := R) (S := S) facets) :
    LinearIndependent k
        ((localizedStanleyReisnerFacetEmbedding
          (k := k) (R := R) (S := S) M facets) ∘ P) ↔
      LinearIndependent k P :=
  linearIndependent_quotientFacetEmbedding_iff
    (localizedStanleyReisnerIdeal (R := R) (S := S) facets)
    (fun F : facets => localizedFacetIdeal (R := R) (S := S) F.1)
    (localizedStanleyReisnerIdeal_eq_iInf_localizedFacetIdeal M facets) P

end

end GaloisForLFunctions.HTGeometry
