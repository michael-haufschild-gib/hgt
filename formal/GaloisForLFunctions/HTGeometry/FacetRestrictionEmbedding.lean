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

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-!
## Birelative anomaly gluing

Two quotient channels need not be ordered.  Their common information is the quotient by the
intersection, while the obstruction to joining independently observed classes is their difference
modulo the sum.  The next declarations package the resulting short exact Mayer--Vietoris law.
-/

/-- The compatibility defect of two quotient observations.  It vanishes precisely when the two
classes can be represented by one ambient element. -/
def birelativeCompatibilityMap
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) :
    (M ⧸ I) × (M ⧸ J) →ₗ[R] M ⧸ (I ⊔ J) :=
  ((Submodule.factor (show I ≤ I ⊔ J from le_sup_left)).comp
      (LinearMap.fst R (M ⧸ I) (M ⧸ J))) -
    ((Submodule.factor (show J ≤ I ⊔ J from le_sup_right)).comp
      (LinearMap.snd R (M ⧸ I) (M ⧸ J)))

/-- A common ambient class gives its two quotient observations. -/
def birelativeCommonLiftMap
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) :
    M ⧸ (I ⊓ J) →ₗ[R] (M ⧸ I) × (M ⧸ J) :=
  (Submodule.factor (show I ⊓ J ≤ I from inf_le_left)).prod
    (Submodule.factor (show I ⊓ J ≤ J from inf_le_right))

@[simp]
theorem birelativeCompatibilityMap_mk
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) (x y : M) :
    birelativeCompatibilityMap I J (I.mkQ x, J.mkQ y) = (I ⊔ J).mkQ (x - y) := by
  rfl

@[simp]
theorem birelativeCommonLiftMap_mk
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) (x : M) :
    birelativeCommonLiftMap I J ((I ⊓ J).mkQ x) = (I.mkQ x, J.mkQ x) := by
  rfl

/-- Common quotient observations retain exactly the class modulo the intersection. -/
theorem birelativeCommonLiftMap_injective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) :
    Function.Injective (birelativeCommonLiftMap I J) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (I ⊓ J) x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (I ⊓ J) y
  apply (Submodule.Quotient.eq (I ⊓ J)).2
  constructor
  · apply (Submodule.Quotient.eq I).1
    exact congrArg Prod.fst hxy
  · apply (Submodule.Quotient.eq J).1
    exact congrArg Prod.snd hxy

/-- **Birelative exactness.**  Compatible pairs are exactly common lifts. -/
theorem range_birelativeCommonLiftMap_eq_ker
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) :
    LinearMap.range (birelativeCommonLiftMap I J) =
      LinearMap.ker (birelativeCompatibilityMap I J) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (I ⊓ J) z
    change birelativeCompatibilityMap I J (I.mkQ a, J.mkQ a) = 0
    rw [birelativeCompatibilityMap_mk]
    simp
  · rintro ⟨x, y⟩ hxy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective J y
    have hxy' : (I ⊔ J).mkQ (a - b) = 0 := by
      simpa only [birelativeCompatibilityMap_mk] using hxy
    have hab : a - b ∈ I ⊔ J := by
      apply (Submodule.Quotient.eq (I ⊔ J)).1
      rw [← sub_eq_zero]
      simpa only [map_sub] using hxy'
    rcases Submodule.mem_sup.1 hab with ⟨i, hi, j, hj, hij⟩
    refine ⟨(I ⊓ J).mkQ (a - i), ?_⟩
    apply Prod.ext
    · apply (Submodule.Quotient.eq I).2
      change a - i - a ∈ I
      have : a - i - a = -i := by abel
      rw [this]
      exact I.neg_mem hi
    · apply (Submodule.Quotient.eq J).2
      change a - i - b ∈ J
      have : a - i - b = j := by
        calc
          a - i - b = (a - b) - i := by abel
          _ = (i + j) - i := by rw [hij]
          _ = j := by abel
      rw [this]
      exact hj

/-- Every compatibility-defect class occurs. -/
theorem birelativeCompatibilityMap_surjective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) :
    Function.Surjective (birelativeCompatibilityMap I J) := by
  intro z
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (I ⊔ J) z
  refine ⟨(I.mkQ a, 0), ?_⟩
  change birelativeCompatibilityMap I J (I.mkQ a, J.mkQ 0) = (I ⊔ J).mkQ a
  rw [birelativeCompatibilityMap_mk]
  simp

/-- Two quotient observations have a common ambient representative exactly when their compatibility
defect vanishes. -/
theorem exists_commonRepresentative_iff_compatible
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) (x : M ⧸ I) (y : M ⧸ J) :
    (∃ a : M, I.mkQ a = x ∧ J.mkQ a = y) ↔
      birelativeCompatibilityMap I J (x, y) = 0 := by
  constructor
  · rintro ⟨a, rfl, rfl⟩
    simpa using (birelativeCompatibilityMap_mk I J a a)
  · intro hxy
    have hmem : (x, y) ∈ LinearMap.ker (birelativeCompatibilityMap I J) := hxy
    rw [← range_birelativeCommonLiftMap_eq_ker I J] at hmem
    rcases hmem with ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (I ⊓ J) z
    exact ⟨a, congrArg Prod.fst hz, congrArg Prod.snd hz⟩

/-- Two common representatives differ by exactly the intersection ambiguity. -/
theorem commonRepresentative_sub_mem_inf
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) {a b : M}
    (hI : I.mkQ a = I.mkQ b) (hJ : J.mkQ a = J.mkQ b) :
    a - b ∈ I ⊓ J := by
  exact ⟨(Submodule.Quotient.eq I).1 hI, (Submodule.Quotient.eq J).1 hJ⟩

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-!
## Higher interaction: pairwise compatibility need not be effective

The two-channel sequence above is always exact.  Starting with three channels, pairwise agreement
can be vacuous while a common ambient representative does not exist.  This is the first abelian
higher-interaction obstruction behind the cubical descent architecture.
-/

/-- Pairwise vanishing of all three birelative compatibility defects. -/
def triplePairwiseCompatible
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J K : Submodule R M) (x : M ⧸ I) (y : M ⧸ J) (z : M ⧸ K) : Prop :=
  birelativeCompatibilityMap I J (x, y) = 0 ∧
    birelativeCompatibilityMap I K (x, z) = 0 ∧
      birelativeCompatibilityMap J K (y, z) = 0

/-- If every pair of channels generates the ambient module, every triple of observations is
pairwise compatible. -/
theorem triplePairwiseCompatible_of_pairwise_sup_eq_top
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J K : Submodule R M)
    (hIJ : I ⊔ J = ⊤) (hIK : I ⊔ K = ⊤) (hJK : J ⊔ K = ⊤)
    (x : M ⧸ I) (y : M ⧸ J) (z : M ⧸ K) :
    triplePairwiseCompatible I J K x y z := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective J y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective K z
  constructor
  · change birelativeCompatibilityMap I J (I.mkQ a, J.mkQ b) = 0
    rw [birelativeCompatibilityMap_mk, hIJ]
    apply (Submodule.Quotient.eq ⊤).2
    simp
  constructor
  · change birelativeCompatibilityMap I K (I.mkQ a, K.mkQ c) = 0
    rw [birelativeCompatibilityMap_mk, hIK]
    apply (Submodule.Quotient.eq ⊤).2
    simp
  · change birelativeCompatibilityMap J K (J.mkQ b, K.mkQ c) = 0
    rw [birelativeCompatibilityMap_mk, hJK]
    apply (Submodule.Quotient.eq ⊤).2
    simp

/-- **Three-channel interaction obstruction.**  Even when all pairwise compatibility tests vanish,
a triple can have no common representative.  The positive obstruction is the surviving class
modulo `(I ⊓ J) ⊔ K`. -/
theorem pairwiseCompatible_without_commonTripleRepresentative
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J K : Submodule R M)
    (hIJ : I ⊔ J = ⊤) (hIK : I ⊔ K = ⊤) (hJK : J ⊔ K = ⊤)
    {v : M} (hv : v ∉ (I ⊓ J) ⊔ K) :
    triplePairwiseCompatible I J K 0 0 (K.mkQ v) ∧
      ¬ ∃ a : M, I.mkQ a = 0 ∧ J.mkQ a = 0 ∧ K.mkQ a = K.mkQ v := by
  constructor
  · exact triplePairwiseCompatible_of_pairwise_sup_eq_top I J K hIJ hIK hJK 0 0 (K.mkQ v)
  · rintro ⟨a, haI, haJ, haK⟩
    have haI_mem : a ∈ I := by
      have hai0 : I.mkQ a = I.mkQ 0 := by simpa using haI
      have := (Submodule.Quotient.eq I).1 hai0
      simpa using this
    have haJ_mem : a ∈ J := by
      have haj0 : J.mkQ a = J.mkQ 0 := by simpa using haJ
      have := (Submodule.Quotient.eq J).1 haj0
      simpa using this
    have havK : a - v ∈ K := (Submodule.Quotient.eq K).1 haK
    apply hv
    apply Submodule.mem_sup.2
    refine ⟨a, ⟨haI_mem, haJ_mem⟩, v - a, ?_, ?_⟩
    · simpa only [neg_sub] using K.neg_mem havK
    · abel

end

end GaloisForLFunctions.HTGeometry
