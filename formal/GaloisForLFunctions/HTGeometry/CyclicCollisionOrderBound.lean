import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Set.Card

/-!
# A faithful cyclic action whose collision classes have at most two members

Let a group act on a set and let `r` be a map invariant under the action whose fibres have at most
two elements.  For any `g` and `x` the three points `x`, `g • x`, `g ^ 2 • x` lie in one fibre, so
two of them coincide, and each case gives `g ^ 2 • x = x`.  If the action is faithful and the group
is cyclic, a generator therefore squares to the identity:

```text
sq_smul_eq_self_of_fibre_le_two    every square acts trivially
natCard_le_two_of_isCyclic         ** the group has at most two elements **
```

This is the group-theoretic half of "a simple fold has inertia of order two": the collision classes
of the reduction bound the orbits, and cyclicity of tame inertia turns that bound on orbits into a
bound on the group.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Three members of a set with at most two elements cannot be pairwise distinct. -/
theorem exists_eq_of_ncard_le_two {X : Type*} {S : Set X} (hfin : S.Finite) (h : S.ncard ≤ 2)
    {a b c : X} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) : a = b ∨ a = c ∨ b = c := by
  by_contra hcon
  have hab : a ≠ b := fun h => hcon (Or.inl h)
  have hac : a ≠ c := fun h => hcon (Or.inr (Or.inl h))
  have hbc : b ≠ c := fun h => hcon (Or.inr (Or.inr h))
  have hsub : ({a, b, c} : Set X) ⊆ S := by
    intro y hy
    rcases hy with rfl | hy
    · exact ha
    rcases hy with rfl | hy
    · exact hb
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hc
  have hcard : ({a, b, c} : Set X).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac]) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by simp [hbc]) (Set.toFinite _), Set.ncard_singleton]
  have := Set.ncard_le_ncard hsub hfin
  omega

/-- **A square acts trivially when every collision class has at most two members.**  If a map is
invariant under the action and each of its fibres has at most two elements, then the square of every
group element fixes every point. -/
theorem sq_smul_eq_self_of_fibre_le_two {G X Y : Type*} [Group G] [MulAction G X]
    (r : X → Y) (hinv : ∀ (g : G) (x : X), r (g • x) = r x)
    (hfib : ∀ x : X, (r ⁻¹' {r x}).Finite ∧ (r ⁻¹' {r x}).ncard ≤ 2)
    (g : G) (x : X) : g ^ 2 • x = x := by
  obtain ⟨hfin, hle⟩ := hfib x
  have hx : x ∈ r ⁻¹' {r x} := rfl
  have h1 : g • x ∈ r ⁻¹' {r x} := by simp [Set.mem_preimage, hinv]
  have h2 : g ^ 2 • x ∈ r ⁻¹' {r x} := by simp [Set.mem_preimage, hinv]
  rcases exists_eq_of_ncard_le_two hfin hle hx h1 h2 with h | h | h
  · calc g ^ 2 • x = g • (g • x) := by rw [pow_two, mul_smul]
      _ = g • x := by conv_lhs => rw [← h]
      _ = x := h.symm
  · exact h.symm
  · have hgx : x = g • x := by
      rw [pow_two, mul_smul] at h
      have hcong := congrArg (fun y : X => g⁻¹ • y) h
      simpa using hcong
    calc g ^ 2 • x = g • (g • x) := by rw [pow_two, mul_smul]
      _ = g • x := by conv_lhs => rw [← hgx]
      _ = x := hgx.symm

/-- **A faithful cyclic action with collision classes of size at most two has order at most two.**
Every square acts trivially, so a generator squares to the identity. -/
theorem natCard_le_two_of_isCyclic {G X Y : Type*} [Group G] [Finite G] [IsCyclic G]
    [MulAction G X] [FaithfulSMul G X]
    (r : X → Y) (hinv : ∀ (g : G) (x : X), r (g • x) = r x)
    (hfib : ∀ x : X, (r ⁻¹' {r x}).Finite ∧ (r ⁻¹' {r x}).ncard ≤ 2) :
    Nat.card G ≤ 2 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := G)
  have hsq : a ^ 2 = 1 :=
    FaithfulSMul.eq_of_smul_eq_smul (α := X)
      (fun x => by rw [sq_smul_eq_self_of_fibre_le_two r hinv hfib a x, one_smul])
  have hord : orderOf a ≤ 2 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hsq)
  have hcard : Nat.card G = orderOf a := (orderOf_eq_card_of_forall_mem_zpowers ha).symm
  omega

end GaloisForLFunctions.HTGeometry
