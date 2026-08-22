import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Basic

/-!
# A faithful cyclic permutation representation with large stabilisers

The orbit bound of `CyclicOrbitOrderBound` is unusable on the critical horizon: every `show`,
`change` or `rw` over the sheet and permutation types there exhausts the elaborator.  This module
states the same conclusion in a form whose only interface is a cardinality inequality of natural
numbers, so the instantiation costs nothing.

```text
repStabilizer                                the pointwise stabiliser, as a subgroup
natCard_le_two_of_isCyclic_of_stabilizer_card
    ** |G| ≤ 2·#{g : ρ g x = x} for every x  ⟹  |G| ≤ 2 **
```

The proof is `Subgroup.pow_index_mem`: a subgroup of a cyclic — hence commutative — group is normal,
so `a ^ [G : H] ∈ H`, and the hypothesis forces the index to be one or two, either of which puts
`a ^ 2` in every point stabiliser.  Faithfulness then makes `a ^ 2 = 1`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The pointwise stabiliser of a point under a permutation representation. -/
def repStabilizer {G X : Type*} [Group G] (ρ : G →* Equiv.Perm X) (x : X) : Subgroup G where
  carrier := {g | ρ g x = x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Equiv.Perm.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv]
    exact (Equiv.symm_apply_eq _).mpr ha.symm

@[simp] theorem mem_repStabilizer {G X : Type*} [Group G] (ρ : G →* Equiv.Perm X) (x : X)
    {g : G} : g ∈ repStabilizer ρ x ↔ ρ g x = x := Iff.rfl

/-- **A faithful cyclic permutation representation whose point stabilisers have index at most two
has order at most two.** -/
theorem natCard_le_two_of_isCyclic_of_stabilizer_card
    {G X : Type*} [Group G] [Finite G] [IsCyclic G]
    (ρ : G →* Equiv.Perm X) (hρ : Function.Injective ρ)
    (h : ∀ x : X, Nat.card G ≤ 2 * Nat.card {g : G // ρ g x = x}) :
    Nat.card G ≤ 2 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := G)
  have hsub : ∀ x : X, Nat.card (repStabilizer ρ x) = Nat.card {g : G // ρ g x = x} :=
    fun _ => rfl
  haveI : ∀ x : X, (repStabilizer ρ x).Normal := fun x =>
    Subgroup.normal_of_isMulCommutative _
  have hsq : ∀ x : X, ρ (a ^ 2) x = x := by
    intro x
    have hmul := Subgroup.card_mul_index (repStabilizer ρ x)
    have hcard : 0 < Nat.card (repStabilizer ρ x) := Nat.card_pos
    have hidx : (repStabilizer ρ x).index ≤ 2 := by
      have h2 : Nat.card (repStabilizer ρ x) * (repStabilizer ρ x).index
          ≤ Nat.card (repStabilizer ρ x) * 2 := by
        rw [hmul, mul_comm, hsub x]
        exact h x
      exact Nat.le_of_mul_le_mul_left h2 hcard
    have hpow : a ^ (repStabilizer ρ x).index ∈ repStabilizer ρ x :=
      Subgroup.pow_index_mem _ a
    have hidx0 : 0 < (repStabilizer ρ x).index := by
      rcases Nat.eq_zero_or_pos (repStabilizer ρ x).index with h0 | h0
      · rw [h0, mul_zero] at hmul
        have := Nat.card_pos (α := G)
        omega
      · exact h0
    have hcases : (repStabilizer ρ x).index = 1 ∨ (repStabilizer ρ x).index = 2 := by omega
    rcases hcases with hI | hI
    · rw [hI, pow_one] at hpow
      have h1 : ρ a x = x := hpow
      have h2 : ρ (a ^ 2) x = ρ a (ρ a x) := by
        rw [pow_two, map_mul, Equiv.Perm.mul_apply]
      rw [h2, h1, h1]
    · rw [hI] at hpow
      exact hpow
  have ha2 : a ^ 2 = 1 := by
    apply hρ
    rw [map_one]
    exact Equiv.ext fun x => hsq x
  have hord : orderOf a ≤ 2 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one ha2)
  have hcard : Nat.card G = orderOf a := (orderOf_eq_card_of_forall_mem_zpowers ha).symm
  omega

end GaloisForLFunctions.HTGeometry
