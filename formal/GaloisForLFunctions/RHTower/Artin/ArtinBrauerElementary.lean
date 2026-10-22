import GaloisForLFunctions.RHTower.Artin.ArtinMonomialCharacter
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Concrete Brauer-elementary subgroup data

Brauer induction uses induced linear characters from `p`-elementary subgroups.  This module makes
that carrier concrete: it records internal cyclic `p'` and `p` parts together with an actual
multiplication equivalence.  It does not assume or prove Brauer induction.
-/

noncomputable section

universe u

namespace GaloisForLFunctions

/-- Data witnessing that a subgroup is Brauer `p`-elementary.  The factorization is internal to
the subgroup carrier and its equivalence is required to agree with multiplication. -/
structure BrauerElementarySubgroup (G : Type u) [Group G] where
  subgroup : Subgroup G
  p : ℕ
  p_prime : Nat.Prime p
  cyclicPart : Subgroup subgroup
  pPart : Subgroup subgroup
  cyclicPart_cyclic : IsCyclic cyclicPart
  cyclicPart_coprime : Nat.Coprime (Nat.card cyclicPart) p
  pPart_isPGroup : IsPGroup p pPart
  multiplicationEquiv : cyclicPart × pPart ≃* subgroup
  multiplicationEquiv_apply (c : cyclicPart) (q : pPart) :
    multiplicationEquiv (c, q) = (c : subgroup) * (q : subgroup)

/-- Concrete indices for the induced-linear generators allowed by integral Brauer induction. -/
def brauerElementaryMonomialIndex (G : Type u) [Group G] :=
  Σ E : BrauerElementarySubgroup G, LinearCharacter E.subgroup

/-- The actual monomial virtual character associated to a concrete Brauer-elementary index. -/
def brauerElementaryMonomialVirtualCharacter
    (G : Type u) [Group G] [Fintype G]
    (q : brauerElementaryMonomialIndex G) : VirtualCharacter G :=
  monomialVirtualCharacter G q.1.subgroup q.2

/-- The cyclic factor in concrete Brauer-elementary data is finite: a prime cannot be coprime to
the zero cardinal. -/
theorem BrauerElementarySubgroup.finite_cyclicPart
    {G : Type u} [Group G] (E : BrauerElementarySubgroup G) : Finite E.cyclicPart := by
  apply Nat.finite_of_card_ne_zero
  intro hzero
  have hpone : E.p = 1 := by
    simpa [hzero] using E.cyclicPart_coprime
  exact E.p_prime.ne_one hpone

/-- In a direct product of a finite `p'` group and a `p`-group, membership in any subgroup is
closed under extraction of the `p` coordinate. -/
theorem subgroup_prod_snd_mem_of_card_coprime
    {C P : Type u} [Group C] [Group P] {p : ℕ} [Fact p.Prime] [Finite C]
    (hC : (Nat.card C).Coprime p) (hP : IsPGroup p P)
    (K : Subgroup (C × P)) {x : C × P} (hx : x ∈ K) :
    (1, x.2) ∈ K := by
  have hpowP :
      x.2 ^ ((orderOf x.2).gcdB (Nat.card C) * (Nat.card C : ℤ)) = x.2 := by
    simpa only [IsPGroup.powEquiv_apply, IsPGroup.powEquiv_symm_apply, zpow_mul,
      zpow_natCast] using
      (hP.powEquiv hC.symm).apply_symm_apply x.2
  have hpowC :
      x.1 ^ ((orderOf x.2).gcdB (Nat.card C) * (Nat.card C : ℤ)) = 1 := by
    rw [mul_comm, zpow_mul, zpow_natCast, pow_card_eq_one', one_zpow]
  have hpow :
      x ^ ((orderOf x.2).gcdB (Nat.card C) * (Nat.card C : ℤ)) = (1, x.2) := by
    apply Prod.ext
    · simpa using hpowC
    · simpa using hpowP
  rw [← hpow]
  exact K.zpow_mem hx _

/-- The same coprime direct-product argument extracts the `p'` coordinate. -/
theorem subgroup_prod_fst_mem_of_card_coprime
    {C P : Type u} [Group C] [Group P] {p : ℕ} [Fact p.Prime] [Finite C]
    (hC : (Nat.card C).Coprime p) (hP : IsPGroup p P)
    (K : Subgroup (C × P)) {x : C × P} (hx : x ∈ K) :
    (x.1, 1) ∈ K := by
  have hsnd : (1, x.2) ∈ K :=
    subgroup_prod_snd_mem_of_card_coprime hC hP K hx
  have hmul : x * (1, x.2)⁻¹ ∈ K := K.mul_mem hx (K.inv_mem hsnd)
  have hid : x * (1, x.2)⁻¹ = (x.1, 1) := by
    ext <;> simp
  rwa [hid] at hmul

/-- A subgroup of a finite direct product of a cyclic `p'` group and a `p`-group is the
direct product of its two projection images.  This is the subgroup-closure step needed when
passing from a Brauer-elementary group to one of its subgroups. -/
theorem subgroup_prod_eq_prod_maps_of_card_coprime
    {C P : Type u} [Group C] [Group P] {p : ℕ} [Fact p.Prime] [Finite C]
    (hC : (Nat.card C).Coprime p) (hP : IsPGroup p P)
    (K : Subgroup (C × P)) :
    K = (K.map (MonoidHom.fst C P)).prod (K.map (MonoidHom.snd C P)) := by
  apply le_antisymm
  · exact Subgroup.le_prod_iff.mpr ⟨le_rfl, le_rfl⟩
  · refine Subgroup.prod_le_iff.mpr ⟨?_, ?_⟩
    · rintro y ⟨c, ⟨x, hx, hxc⟩, rfl⟩
      subst hxc
      simpa using subgroup_prod_fst_mem_of_card_coprime hC hP K hx
    · rintro y ⟨q, ⟨x, hx, hxq⟩, rfl⟩
      subst hxq
      simpa using subgroup_prod_snd_mem_of_card_coprime hC hP K hx

/-- Pulling a subgroup of a concrete Brauer-elementary subgroup back along its recorded product
equivalence permits extraction of its `p` coordinate. -/
theorem BrauerElementarySubgroup.preimage_snd_mem
    {G : Type u} [Group G] (E : BrauerElementarySubgroup G)
    (K : Subgroup E.subgroup) {x : E.cyclicPart × E.pPart}
    (hx : x ∈ K.comap E.multiplicationEquiv.toMonoidHom) :
    (1, x.2) ∈ K.comap E.multiplicationEquiv.toMonoidHom := by
  letI : Finite E.cyclicPart := E.finite_cyclicPart
  letI : Fact E.p.Prime := ⟨E.p_prime⟩
  exact subgroup_prod_snd_mem_of_card_coprime E.cyclicPart_coprime E.pPart_isPGroup _ hx

/-- Pulling back along the recorded product equivalence also permits extraction of the `p'`
coordinate. -/
theorem BrauerElementarySubgroup.preimage_fst_mem
    {G : Type u} [Group G] (E : BrauerElementarySubgroup G)
    (K : Subgroup E.subgroup) {x : E.cyclicPart × E.pPart}
    (hx : x ∈ K.comap E.multiplicationEquiv.toMonoidHom) :
    (x.1, 1) ∈ K.comap E.multiplicationEquiv.toMonoidHom := by
  letI : Finite E.cyclicPart := E.finite_cyclicPart
  letI : Fact E.p.Prime := ⟨E.p_prime⟩
  exact subgroup_prod_fst_mem_of_card_coprime E.cyclicPart_coprime E.pPart_isPGroup _ hx

end GaloisForLFunctions
