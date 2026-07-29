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
      change birelativeCompatibilityMap I J (I.mkQ a, J.mkQ b) = 0 at hxy
      rw [birelativeCompatibilityMap_mk] at hxy
      exact hxy
    have hab : a - b ∈ I ⊔ J := by
      apply (Submodule.Quotient.eq (I ⊔ J)).1
      rw [← sub_eq_zero]
      change (I ⊔ J).mkQ a - (I ⊔ J).mkQ b = 0
      rw [← map_sub]
      exact hxy'
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

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Exact three-channel interaction quotient.**  For the triple whose first two observations
vanish and whose third is represented by `v`, common effectivity is equivalent to vanishing of the
class of `v` modulo `(I ⊓ J) ⊔ K`. -/
theorem zero_zero_third_has_commonRepresentative_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J K : Submodule R M) (v : M) :
    (∃ a : M, I.mkQ a = 0 ∧ J.mkQ a = 0 ∧ K.mkQ a = K.mkQ v) ↔
      v ∈ (I ⊓ J) ⊔ K := by
  constructor
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
    apply Submodule.mem_sup.2
    refine ⟨a, ⟨haI_mem, haJ_mem⟩, v - a, ?_, ?_⟩
    · simpa only [neg_sub] using K.neg_mem havK
    · abel
  · intro hv
    rcases Submodule.mem_sup.1 hv with ⟨a, ha, k, hk, hak⟩
    refine ⟨a, ?_, ?_, ?_⟩
    · change I.mkQ a = I.mkQ 0
      apply (Submodule.Quotient.eq I).2
      simpa using ha.1
    · change J.mkQ a = J.mkQ 0
      apply (Submodule.Quotient.eq J).2
      simpa using ha.2
    · apply (Submodule.Quotient.eq K).2
      have : a - v = -k := by rw [← hak]; abel
      rw [this]
      exact K.neg_mem hk

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-!
## Distributive finite-family fracture descent

Two-channel exactness extends to a finite family precisely when the family of gauge submodules
obeys the required finite distributivity law.  Under that law, pairwise compatibility is already
global effectivity, and the ambiguity of the common representative is the finite intersection.
-/

/-- Every pair of observations indexed by `s` has zero birelative compatibility defect. -/
def familyPairwiseCompatibleOn
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J : ι → Submodule R M) (s : Finset ι)
    (x : (i : ι) → M ⧸ J i) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s,
    birelativeCompatibilityMap (J i) (J j) (x i, x j) = 0

/-- The finite distributivity law needed to glue quotient observations one channel at a time. -/
def IsFractureDistributive
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J : ι → Submodule R M) : Prop :=
  ∀ (i : ι) (s : Finset ι),
    J i ⊔ s.inf J = s.inf (fun j => J i ⊔ J j)

/-- Pairwise-compatible quotient observations in a distributive finite fracture family have one
common ambient representative. -/
theorem exists_commonFamilyRepresentative_of_pairwiseCompatible
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [DecidableEq ι]
    (J : ι → Submodule R M) (hJ : IsFractureDistributive J)
    (s : Finset ι) (x : (i : ι) → M ⧸ J i)
    (hx : familyPairwiseCompatibleOn J s x) :
    ∃ a : M, ∀ i ∈ s, (J i).mkQ a = x i := by
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert i s hi ih =>
      have hxs : familyPairwiseCompatibleOn J s x := by
        intro j hj k hk
        exact hx j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
      obtain ⟨a, ha⟩ := ih hxs
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective (J i) (x i)
      have h_each : ∀ j ∈ s, b - a ∈ J i ⊔ J j := by
        intro j hj
        have hc := hx i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        rw [← hb, ← ha j hj] at hc
        have hc' : (J i ⊔ J j).mkQ (b - a) = 0 := by
          change birelativeCompatibilityMap (J i) (J j)
            ((J i).mkQ b, (J j).mkQ a) = 0 at hc
          rw [birelativeCompatibilityMap_mk] at hc
          exact hc
        apply (Submodule.Quotient.eq (J i ⊔ J j)).1
        rw [← sub_eq_zero]
        change (J i ⊔ J j).mkQ b - (J i ⊔ J j).mkQ a = 0
        rw [← map_sub]
        exact hc'
      have h_inf : b - a ∈ s.inf (fun j => J i ⊔ J j) := by
        simpa only [Finset.inf_eq_iInf, Submodule.mem_iInf] using h_each
      rw [← hJ i s] at h_inf
      rcases Submodule.mem_sup.1 h_inf with ⟨u, hu, k, hk, huk⟩
      refine ⟨a + k, ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        rw [← hb]
        apply (Submodule.Quotient.eq (J i)).2
        have : a + k - b = -u := by
          calc
            a + k - b = k - (b - a) := by abel
            _ = k - (u + k) := by rw [huk]
            _ = -u := by abel
        rw [this]
        exact (J i).neg_mem hu
      · have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hji
        rw [← ha j hjs]
        apply (Submodule.Quotient.eq (J j)).2
        have : a + k - a = k := by abel
        rw [this]
        have hle : s.inf J ≤ J j := Finset.inf_le_of_le hjs le_rfl
        exact hle hk

/-- **Distributive fracture H0 law.**  Pairwise compatibility is equivalent to existence of a
common representative for every finite distributive family of quotient channels. -/
theorem exists_commonFamilyRepresentative_iff
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [DecidableEq ι]
    (J : ι → Submodule R M) (hJ : IsFractureDistributive J)
    (s : Finset ι) (x : (i : ι) → M ⧸ J i) :
    (∃ a : M, ∀ i ∈ s, (J i).mkQ a = x i) ↔
      familyPairwiseCompatibleOn J s x := by
  constructor
  · rintro ⟨a, ha⟩ i hi j hj
    rw [← ha i hi, ← ha j hj]
    rw [birelativeCompatibilityMap_mk]
    simp
  · exact exists_commonFamilyRepresentative_of_pairwiseCompatible J hJ s x

/-- Common representatives of a complete finite family differ by the intersection of all gauge
submodules. -/
theorem commonFamilyRepresentative_sub_mem_inf
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [DecidableEq ι]
    (J : ι → Submodule R M) (s : Finset ι) {a b : M}
    (h : ∀ i ∈ s, (J i).mkQ a = (J i).mkQ b) :
    a - b ∈ s.inf J := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.inf_insert]
      constructor
      · exact (Submodule.Quotient.eq (J i)).1
          (h i (Finset.mem_insert_self i s))
      · apply ih
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Finset MvPolynomial

noncomputable section

/-!
## Effective descent for coordinate-facet channels

Arbitrary quotient channels can have genuine higher interaction obstructions.  Coordinate-facet
ideals are different: their monomial support law makes their finite lattice distributive.  Hence
pairwise-compatible facet observations have one global polynomial representative, unique modulo
the Stanley--Reisner nonface ideal.
-/

variable {R α : Type*} [CommRing R] [DecidableEq α]

/-- The sum of two coordinate-facet ideals is the coordinate ideal of the facet intersection. -/
theorem facetIdeal_sup (F G : Finset α) :
    facetIdeal R F ⊔ facetIdeal R G = facetIdeal R (F ∩ G) := by
  rw [facetIdeal, facetIdeal, facetIdeal, ← Ideal.span_union, ← Set.image_union]
  congr 1
  ext i
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with hxF | hxG
    · change x ∉ F at hxF
      refine ⟨x, ?_, rfl⟩
      change x ∉ F ∩ G
      intro hxFG
      exact hxF (Finset.mem_inter.mp hxFG).1
    · change x ∉ G at hxG
      refine ⟨x, ?_, rfl⟩
      change x ∉ F ∩ G
      intro hxFG
      exact hxG (Finset.mem_inter.mp hxFG).2
  · rintro ⟨x, hx, rfl⟩
    change x ∉ F ∩ G at hx
    have hx' : x ∉ F ∨ x ∉ G := by
      simpa only [Finset.mem_inter, not_and_or] using hx
    refine ⟨x, ?_, rfl⟩
    change (x ∉ F) ∨ (x ∉ G)
    exact hx'

/-- Coordinate-facet ideals obey the finite distributivity law needed for fracture descent. -/
theorem facetIdeal_isFractureDistributive :
    IsFractureDistributive
      (facetIdeal R : Finset α → Ideal (MvPolynomial α R)) := by
  intro F s
  apply le_antisymm
  · apply Finset.le_inf
    intro G hG
    exact sup_le_sup_left (Finset.inf_le_of_le hG le_rfl) _
  · intro P hP
    rw [MvPolynomial.as_sum P]
    apply Ideal.sum_mem
    intro d hd
    by_cases hdF : d.support ⊆ F
    · apply (show s.inf (facetIdeal R) ≤
        facetIdeal R F ⊔ s.inf (facetIdeal R) from le_sup_right)
      rw [Finset.inf_eq_iInf]
      simp only [Ideal.mem_iInf]
      intro G hG
      rw [mem_facetIdeal_iff]
      intro e he heG
      have hcoeff : coeff d P ≠ 0 := Finsupp.mem_support_iff.mp hd
      have hed : d = e := by simpa [hcoeff] using he
      subst e
      have hPG : P ∈ facetIdeal R (F ∩ G) := by
        rw [← facetIdeal_sup]
        have hle : s.inf (fun G => facetIdeal R F ⊔ facetIdeal R G) ≤
            facetIdeal R F ⊔ facetIdeal R G :=
          Finset.inf_le_of_le hG le_rfl
        exact hle hP
      exact (mem_facetIdeal_iff (R := R) (F ∩ G) P).mp hPG d hd
        (Finset.subset_inter hdF heG)
    · apply (show facetIdeal R F ≤
        facetIdeal R F ⊔ s.inf (facetIdeal R) from le_sup_left)
      rw [mem_facetIdeal_iff]
      intro e he heF
      have hcoeff : coeff d P ≠ 0 := Finsupp.mem_support_iff.mp hd
      have hed : d = e := by simpa [hcoeff] using he
      subst e
      exact hdF heF

/-- **Coordinate-facet effectivity.**  A finite packet of facet quotient observations has one
global polynomial representative exactly when all of its pairwise compatibility defects vanish. -/
theorem exists_commonFacetPolynomialRepresentative_iff
    (s : Finset (Finset α))
    (x : (F : Finset α) → MvPolynomial α R ⧸ (facetIdeal R F)) :
    (∃ P : MvPolynomial α R, ∀ F ∈ s, (facetIdeal R F).mkQ P = x F) ↔
      familyPairwiseCompatibleOn (facetIdeal R) s x :=
  exists_commonFamilyRepresentative_iff
    (facetIdeal R) facetIdeal_isFractureDistributive s x

/-- Two global representatives of the same complete finite facet packet differ by the
Stanley--Reisner nonface ideal of that facet family. -/
theorem commonFacetPolynomialRepresentative_sub_mem_stanleyReisnerIdeal
    (s : Finset (Finset α)) {P Q : MvPolynomial α R}
    (h : ∀ F ∈ s, (facetIdeal R F).mkQ P = (facetIdeal R F).mkQ Q) :
    P - Q ∈ stanleyReisnerIdeal R s := by
  rw [stanleyReisnerIdeal_eq_inf_facetIdeal]
  exact commonFamilyRepresentative_sub_mem_inf (facetIdeal R) s h

end

end GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-!
## Calibrated fracture incidence

Compatible local observations determine a torsor under the intersection of the gauge submodules.
A calibration does two logically different jobs on that torsor.  Its image on the intersection
controls existence of a prescribed calibrated lift; its kernel on the intersection controls
uniqueness.  The quotient by the image is the exact residual incidence obstruction.
-/

/-- The obstruction to changing a common representative `a` to one with calibration `target`,
measured modulo all calibration changes invisible to the finite fracture packet. -/
def calibratedFractureDefect
    {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : ι → Submodule R M) (s : Finset ι)
    (calibration : M →ₗ[R] N) (a : M) (target : N) :
    N ⧸ (s.inf J).map calibration :=
  ((s.inf J).map calibration).mkQ (target - calibration a)

/-- The calibrated defect is independent of which common representative of the same finite
fracture packet is used to compute it. -/
theorem calibratedFractureDefect_eq_of_commonRepresentatives
    {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [DecidableEq ι]
    (J : ι → Submodule R M) (s : Finset ι)
    (calibration : M →ₗ[R] N) {a b : M} (target : N)
    (h : ∀ i ∈ s, (J i).mkQ a = (J i).mkQ b) :
    calibratedFractureDefect J s calibration a target =
      calibratedFractureDefect J s calibration b target := by
  apply (Submodule.Quotient.eq ((s.inf J).map calibration)).2
  have hab : a - b ∈ s.inf J :=
    commonFamilyRepresentative_sub_mem_inf J s h
  have hba : b - a ∈ s.inf J := by
    simpa only [neg_sub] using (s.inf J).neg_mem hab
  have hcalc :
      (target - calibration a) - (target - calibration b) =
        calibration (b - a) := by
    rw [map_sub]
    abel
  rw [hcalc]
  exact Submodule.mem_map_of_mem hba

/-- **Exact calibrated-incidence obstruction.**  Once one common representative `a` exists, a
representative with prescribed calibration exists exactly when the calibrated fracture defect
vanishes in the quotient by the calibration image of the residual gauge intersection. -/
theorem exists_calibratedFamilyRepresentative_iff_defect_eq_zero
    {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [DecidableEq ι]
    (J : ι → Submodule R M) (s : Finset ι)
    (x : (i : ι) → M ⧸ J i)
    (calibration : M →ₗ[R] N) (a : M) (target : N)
    (ha : ∀ i ∈ s, (J i).mkQ a = x i) :
    (∃ b : M, (∀ i ∈ s, (J i).mkQ b = x i) ∧ calibration b = target) ↔
      calibratedFractureDefect J s calibration a target = 0 := by
  constructor
  · rintro ⟨b, hb, hcal⟩
    apply (Submodule.Quotient.eq ((s.inf J).map calibration)).2
    have hba : b - a ∈ s.inf J :=
      commonFamilyRepresentative_sub_mem_inf J s (by
        intro i hi
        exact (hb i hi).trans (ha i hi).symm)
    change target - calibration a - 0 ∈ (s.inf J).map calibration
    rw [sub_zero, ← hcal, ← map_sub]
    exact Submodule.mem_map_of_mem hba
  · intro hzero
    have hmem : target - calibration a ∈ (s.inf J).map calibration := by
      change ((s.inf J).map calibration).mkQ (target - calibration a) = 0 at hzero
      exact (Submodule.Quotient.mk_eq_zero ((s.inf J).map calibration)).mp hzero
    rcases hmem with ⟨k, hk, hcal⟩
    refine ⟨a + k, ?_, ?_⟩
    · intro i hi
      rw [← ha i hi]
      apply (Submodule.Quotient.eq (J i)).2
      change a + k - a ∈ J i
      rw [add_sub_cancel_left]
      have hle : s.inf J ≤ J i := Finset.inf_le_of_le hi le_rfl
      exact hle hk
    · rw [map_add, hcal]
      abel

/-- Two representatives with the same finite fracture packet and the same calibration differ by
exactly an element of the gauge intersection killed by the calibration. -/
theorem calibratedFamilyRepresentative_sub_mem_inf_inf_ker
    {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [DecidableEq ι]
    (J : ι → Submodule R M) (s : Finset ι)
    (calibration : M →ₗ[R] N) {a b : M}
    (hlocal : ∀ i ∈ s, (J i).mkQ a = (J i).mkQ b)
    (hcal : calibration a = calibration b) :
    a - b ∈ s.inf J ⊓ LinearMap.ker calibration := by
  constructor
  · exact commonFamilyRepresentative_sub_mem_inf J s hlocal
  · change calibration (a - b) = 0
    rw [map_sub, hcal, sub_self]

/-- If the calibration kills no nonzero residual gauge, a calibrated representative is unique. -/
theorem calibratedFamilyRepresentative_eq_of_inf_inf_ker_eq_bot
    {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [DecidableEq ι]
    (J : ι → Submodule R M) (s : Finset ι)
    (calibration : M →ₗ[R] N) {a b : M}
    (hlocal : ∀ i ∈ s, (J i).mkQ a = (J i).mkQ b)
    (hcal : calibration a = calibration b)
    (hseparates : s.inf J ⊓ LinearMap.ker calibration = ⊥) :
    a = b := by
  apply sub_eq_zero.mp
  have hmem := calibratedFamilyRepresentative_sub_mem_inf_inf_ker
    J s calibration hlocal hcal
  rw [hseparates] at hmem
  simpa using hmem

/-- **Pointed fracture reconstruction.**  If the calibration realizes every value along the
residual gauge intersection and separates that intersection, then every compatible finite packet
and every prescribed calibration have one unique common representative. -/
theorem existsUnique_calibratedFamilyRepresentative
    {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [DecidableEq ι]
    (J : ι → Submodule R M) (hJ : IsFractureDistributive J)
    (s : Finset ι) (x : (i : ι) → M ⧸ J i)
    (hx : familyPairwiseCompatibleOn J s x)
    (calibration : M →ₗ[R] N) (target : N)
    (hsurjective : (s.inf J).map calibration = ⊤)
    (hseparates : s.inf J ⊓ LinearMap.ker calibration = ⊥) :
    ∃! a : M, (∀ i ∈ s, (J i).mkQ a = x i) ∧ calibration a = target := by
  obtain ⟨a, ha⟩ :=
    exists_commonFamilyRepresentative_of_pairwiseCompatible J hJ s x hx
  have hdefect : calibratedFractureDefect J s calibration a target = 0 := by
    change ((s.inf J).map calibration).mkQ (target - calibration a) = 0
    exact (Submodule.Quotient.mk_eq_zero ((s.inf J).map calibration)).mpr (by
      rw [hsurjective]
      simp)
  obtain ⟨b, hb, hcal⟩ :=
    (exists_calibratedFamilyRepresentative_iff_defect_eq_zero
      J s x calibration a target ha).2 hdefect
  refine ⟨b, ⟨hb, hcal⟩, ?_⟩
  intro c hc
  exact calibratedFamilyRepresentative_eq_of_inf_inf_ker_eq_bot
    J s calibration
    (by
      intro i hi
      exact (hc.1 i hi).trans (hb i hi).symm)
    (hc.2.trans hcal.symm) hseparates

end

end GaloisForLFunctions.HTGeometry
