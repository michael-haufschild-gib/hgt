import GaloisForLFunctions.RHTower.Artin.ArtinBrauerElementarySpan
import GaloisForLFunctions.RHTower.Artin.ArtinNilpotentGroupsAreMonomial

/-!
# Brauer's induction theorem

**Theorem** (`brauer_induction`). Every virtual character of a finite group `G` is an integer
combination of characters induced from linear characters of Brauer-elementary subgroups:

  `AddSubgroup.closure (Set.range (brauerElementaryMonomialVirtualCharacter G)) = ⊤`.

* The virtual characters are spanned by the characters induced from Brauer-elementary subgroups
  (`inducedSpan_brauerElementaryFamily`).
* A Brauer-elementary group is the product of a cyclic group and a `p`-group, so it is nilpotent
  (`BrauerElementarySubgroup.isNilpotent`), and its characters are integer combinations of
  characters induced from linear characters of its subgroups.
* A subgroup `K` of a Brauer-elementary subgroup is Brauer-elementary
  (`mem_brauerElementaryFamily_of_le`): it is the product of its intersections with the two
  factors, because the two coordinates of an element of `K` lie in `K`.
* Induction in stages.
-/

open scoped Classical BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

variable {G : Type u} [Group G]

/-! ### Brauer-elementary groups are nilpotent -/

/-- A finite Brauer-elementary group is nilpotent. -/
theorem BrauerElementarySubgroup.isNilpotent [Finite G] (E : BrauerElementarySubgroup G) :
    Group.IsNilpotent E.subgroup := by
  haveI : Fact E.p.Prime := ⟨E.p_prime⟩
  haveI : Group.IsNilpotent E.cyclicPart := by
    haveI := E.cyclicPart_cyclic
    letI : CommGroup E.cyclicPart := IsCyclic.commGroup
    exact CommGroup.isNilpotent
  haveI : Group.IsNilpotent E.pPart := E.pPart_isPGroup.isNilpotent
  exact Group.nilpotent_of_mulEquiv E.multiplicationEquiv

/-- The two factors of a Brauer-elementary subgroup commute. -/
theorem BrauerElementarySubgroup.commute (E : BrauerElementarySubgroup G) (c : E.cyclicPart)
    (q : E.pPart) : Commute (c : E.subgroup) (q : E.subgroup) := by
  have hmul : ((1 : E.cyclicPart), q) * (c, (1 : E.pPart)) = (c, q) :=
    Prod.ext (one_mul c) (mul_one q)
  have h := congrArg E.multiplicationEquiv hmul
  rw [map_mul, E.multiplicationEquiv_apply, E.multiplicationEquiv_apply,
    E.multiplicationEquiv_apply, OneMemClass.coe_one, OneMemClass.coe_one, one_mul, mul_one] at h
  exact h.symm

/-! ### Subgroups of Brauer-elementary subgroups -/

section Subgroups

variable (E : BrauerElementarySubgroup G) {K : Subgroup G} (hK : K ≤ E.subgroup)

/-- The part of `K` in the cyclic factor. -/
def BrauerElementarySubgroup.cyclicPartOf : Subgroup K :=
  E.cyclicPart.comap (Subgroup.inclusion hK)

/-- The part of `K` in the `p`-factor. -/
def BrauerElementarySubgroup.pPartOf : Subgroup K :=
  E.pPart.comap (Subgroup.inclusion hK)

/-- The product map of the two parts of `K`. -/
def BrauerElementarySubgroup.productHomOf : E.cyclicPartOf hK × E.pPartOf hK →* K :=
  (E.cyclicPartOf hK).subtype.noncommCoprod (E.pPartOf hK).subtype fun c q =>
    Commute.of_map (Subgroup.inclusion_injective hK)
      (E.commute ⟨Subgroup.inclusion hK c, c.2⟩ ⟨Subgroup.inclusion hK q, q.2⟩)

theorem BrauerElementarySubgroup.productHomOf_injective :
    Function.Injective (E.productHomOf hK) := by
  have hinj := Subgroup.inclusion_injective hK
  rw [injective_iff_map_eq_one]
  rintro ⟨c, q⟩ h
  have h0 : (c : K) * (q : K) = 1 := h
  have h2 : E.multiplicationEquiv
      (⟨Subgroup.inclusion hK c, c.2⟩, ⟨Subgroup.inclusion hK q, q.2⟩) = 1 := by
    rw [E.multiplicationEquiv_apply]
    show Subgroup.inclusion hK (c : K) * Subgroup.inclusion hK (q : K) = 1
    rw [← map_mul, h0, map_one]
  have h3 := (MulEquiv.map_eq_one_iff E.multiplicationEquiv).mp h2
  have hc : Subgroup.inclusion hK (c : K) = 1 :=
    congrArg (fun x : E.cyclicPart × E.pPart => (x.1 : E.subgroup)) h3
  have hq : Subgroup.inclusion hK (q : K) = 1 :=
    congrArg (fun x : E.cyclicPart × E.pPart => (x.2 : E.subgroup)) h3
  exact Prod.ext (Subtype.ext (hinj (hc.trans (map_one _).symm)))
    (Subtype.ext (hinj (hq.trans (map_one _).symm)))

/-- **Every element of `K` is the product of its two coordinates, and they lie in `K`.** -/
theorem BrauerElementarySubgroup.productHomOf_surjective :
    Function.Surjective (E.productHomOf hK) := by
  intro k
  obtain ⟨x, hx⟩ : ∃ x : E.cyclicPart × E.pPart,
      E.multiplicationEquiv x = Subgroup.inclusion hK k :=
    ⟨E.multiplicationEquiv.symm (Subgroup.inclusion hK k), MulEquiv.apply_symm_apply _ _⟩
  have hxK : x ∈ (K.subgroupOf E.subgroup).comap E.multiplicationEquiv.toMonoidHom := by
    show E.multiplicationEquiv x ∈ K.subgroupOf E.subgroup
    rw [hx]
    exact Subgroup.mem_subgroupOf.mpr k.2
  -- the two coordinates lie in `K`
  have hc : (((x.1 : E.cyclicPart) : E.subgroup) : G) ∈ K := by
    have h1 := Subgroup.mem_subgroupOf.mp
      (show E.multiplicationEquiv (x.1, 1) ∈ K.subgroupOf E.subgroup from
        E.preimage_fst_mem (K.subgroupOf E.subgroup) hxK)
    rwa [E.multiplicationEquiv_apply, OneMemClass.coe_one, mul_one] at h1
  have hq : (((x.2 : E.pPart) : E.subgroup) : G) ∈ K := by
    have h1 := Subgroup.mem_subgroupOf.mp
      (show E.multiplicationEquiv (1, x.2) ∈ K.subgroupOf E.subgroup from
        E.preimage_snd_mem (K.subgroupOf E.subgroup) hxK)
    rwa [E.multiplicationEquiv_apply, OneMemClass.coe_one, one_mul] at h1
  have hc' : (⟨_, hc⟩ : K) ∈ E.cyclicPartOf hK := by
    show Subgroup.inclusion hK ⟨_, hc⟩ ∈ E.cyclicPart
    have e : Subgroup.inclusion hK ⟨_, hc⟩ = (x.1 : E.subgroup) := Subtype.ext rfl
    rw [e]
    exact x.1.2
  have hq' : (⟨_, hq⟩ : K) ∈ E.pPartOf hK := by
    show Subgroup.inclusion hK ⟨_, hq⟩ ∈ E.pPart
    have e : Subgroup.inclusion hK ⟨_, hq⟩ = (x.2 : E.subgroup) := Subtype.ext rfl
    rw [e]
    exact x.2.2
  refine ⟨(⟨⟨_, hc⟩, hc'⟩, ⟨⟨_, hq⟩, hq'⟩), Subtype.ext ?_⟩
  show (((x.1 : E.cyclicPart) : E.subgroup) : G) * (((x.2 : E.pPart) : E.subgroup) : G) = k
  have h := congrArg (fun h : E.subgroup => (h : G)) (E.multiplicationEquiv_apply x.1 x.2)
  rw [Prod.mk.eta, hx] at h
  exact h.symm

include E hK in
/-- **A subgroup of a Brauer-elementary subgroup is Brauer-elementary.** -/
theorem mem_brauerElementaryFamily_of_le : K ∈ brauerElementaryFamily G := by
  haveI := E.finite_cyclicPart
  haveI := E.cyclicPart_cyclic
  have hinj := Subgroup.inclusion_injective hK
  -- the cyclic part of `K` embeds into the cyclic factor
  have hCinj : Function.Injective ((Subgroup.inclusion hK).subgroupComap E.cyclicPart) :=
    fun a b h => Subtype.ext (hinj (congrArg Subtype.val h))
  exact ⟨{
    subgroup := K
    p := E.p
    p_prime := E.p_prime
    cyclicPart := E.cyclicPartOf hK
    pPart := E.pPartOf hK
    cyclicPart_cyclic :=
      isCyclic_of_injective ((Subgroup.inclusion hK).subgroupComap E.cyclicPart) hCinj
    cyclicPart_coprime :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_injective _ hCinj) E.cyclicPart_coprime
    pPart_isPGroup := E.pPart_isPGroup.comap_of_injective (Subgroup.inclusion hK) hinj
    multiplicationEquiv := MulEquiv.ofBijective (E.productHomOf hK)
      ⟨E.productHomOf_injective hK, E.productHomOf_surjective hK⟩
    multiplicationEquiv_apply := fun c q => rfl }, rfl⟩

end Subgroups

/-! ### The theorem -/

variable [Fintype G]

/-- The integer span of the characters induced from linear characters of Brauer-elementary
subgroups. -/
def brauerMonomialSpan (G : Type u) [Group G] [Fintype G] : AddSubgroup (G → ℂ) :=
  AddSubgroup.closure {f | ∃ K ∈ brauerElementaryFamily G, ∃ χ : LinearCharacter K,
    f = inducedFunction K fun k => ((χ k : ℂˣ) : ℂ)}

theorem brauerMonomialSpan_le : brauerMonomialSpan G ≤ virtualCharacterGroup G := by
  rw [brauerMonomialSpan, AddSubgroup.closure_le]
  rintro f ⟨K, -, χ, rfl⟩
  exact AddSubgroup.subset_closure
    (inducedFunction_mem_fdCharacterSet K (linearCharacter_mem_fdCharacterSet χ))

/-- A character induced from a Brauer-elementary subgroup is an integer combination of
characters induced from linear characters of Brauer-elementary subgroups. -/
theorem inducedFunction_mem_brauerMonomialSpan (E : BrauerElementarySubgroup G) {χ : E.subgroup → ℂ}
    (hχ : χ ∈ fdCharacterSet E.subgroup) : inducedFunction E.subgroup χ ∈ brauerMonomialSpan G := by
  haveI := E.isNilpotent
  have hmono := fdCharacterSet_subset_monomialSpan_of_nilpotent E.subgroup hχ
  have hle : monomialSpan E.subgroup ≤
      (brauerMonomialSpan G).comap (inducedFunctionHom E.subgroup) := by
    rw [monomialSpan, AddSubgroup.closure_le]
    rintro f ⟨L, ψ, rfl⟩
    show inducedFunction E.subgroup (inducedFunction L _) ∈ brauerMonomialSpan G
    rw [inducedFunction_inducedFunction]
    exact AddSubgroup.subset_closure ⟨L.map E.subgroup.subtype,
      mem_brauerElementaryFamily_of_le E (Subgroup.map_subtype_le L),
      ψ.comp (L.equivMapOfInjective E.subgroup.subtype
        E.subgroup.subtype_injective).symm.toMonoidHom, rfl⟩
  exact hle hmono

/-- **Brauer's induction theorem, for functions**: the virtual characters are the integer
combinations of characters induced from linear characters of Brauer-elementary subgroups. -/
theorem brauerMonomialSpan_eq : brauerMonomialSpan G = virtualCharacterGroup G := by
  refine le_antisymm brauerMonomialSpan_le ?_
  rw [← inducedSpan_brauerElementaryFamily, inducedSpan, AddSubgroup.closure_le]
  rintro f ⟨H, ⟨E, rfl⟩, χ, hχ, rfl⟩
  exact inducedFunction_mem_brauerMonomialSpan E hχ

/-- **Brauer's induction theorem.** Every virtual character of a finite group is an integer
combination of characters induced from linear characters of Brauer-elementary subgroups. -/
theorem brauer_induction :
    AddSubgroup.closure (Set.range (brauerElementaryMonomialVirtualCharacter G)) = ⊤ := by
  rw [eq_top_iff]
  rintro θ -
  have key : ∀ f ∈ brauerMonomialSpan G, ∀ hf : f ∈ virtualCharacterGroup G,
      (⟨f, hf⟩ : VirtualCharacter G) ∈
        AddSubgroup.closure (Set.range (brauerElementaryMonomialVirtualCharacter G)) := by
    intro f hf
    refine AddSubgroup.closure_induction
      (p := fun f _ => ∀ hf : f ∈ virtualCharacterGroup G, (⟨f, hf⟩ : VirtualCharacter G) ∈
        AddSubgroup.closure (Set.range (brauerElementaryMonomialVirtualCharacter G)))
      ?_ ?_ ?_ ?_ hf
    · rintro f ⟨K, ⟨E, rfl⟩, χ, rfl⟩ hf'
      have e : (⟨_, hf'⟩ : VirtualCharacter G) =
          brauerElementaryMonomialVirtualCharacter G ⟨E, χ⟩ :=
        Subtype.ext (monomialVirtualCharacter_val E.subgroup χ).symm
      rw [e]
      exact AddSubgroup.subset_closure ⟨_, rfl⟩
    · intro h0
      exact zero_mem _
    · intro x y hx hy ihx ihy hxy
      exact add_mem (ihx (brauerMonomialSpan_le hx)) (ihy (brauerMonomialSpan_le hy))
    · intro x hx ihx hneg
      exact neg_mem (ihx (brauerMonomialSpan_le hx))
  exact key θ.val (brauerMonomialSpan_eq (G := G) ▸ θ.2) θ.2

end GaloisForLFunctions
