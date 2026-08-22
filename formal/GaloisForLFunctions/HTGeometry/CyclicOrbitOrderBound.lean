import GaloisForLFunctions.HTGeometry.CyclicCollisionOrderBound

/-!
# A faithful cyclic action with small orbits

`CyclicCollisionOrderBound` bounds a tame group through the *fibres* of an invariant label.  The
ramification dictionary produces the same conclusion from the *orbits* instead, which is what the
inertia action on the sheets of a cover delivers: the orbit of a sheet has as many elements as the
ramification index of the place it sits over.

```text
sq_smul_eq_self_of_orbit_le_two    every square acts trivially
natCard_le_two_of_isCyclic_of_orbit  ** |G| ≤ 2 **
```

The argument is the same three-point one: `x`, `g • x` and `g ^ 2 • x` all lie in the orbit of `x`,
so two of them coincide, and each case forces `g ^ 2 • x = x`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A square acts trivially when every orbit has at most two members.** -/
theorem sq_smul_eq_self_of_orbit_le_two {G X : Type*} [Group G] [MulAction G X]
    (horb : ∀ x : X, (MulAction.orbit G x).Finite ∧ (MulAction.orbit G x).ncard ≤ 2)
    (g : G) (x : X) : g ^ 2 • x = x := by
  obtain ⟨hfin, hle⟩ := horb x
  have hx : x ∈ MulAction.orbit G x := MulAction.mem_orbit_self x
  have h1 : g • x ∈ MulAction.orbit G x := MulAction.mem_orbit x g
  have h2 : g ^ 2 • x ∈ MulAction.orbit G x := MulAction.mem_orbit x (g ^ 2)
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

/-- **A faithful cyclic action with orbits of size at most two has order at most two.** -/
theorem natCard_le_two_of_isCyclic_of_orbit {G X : Type*} [Group G] [Finite G] [IsCyclic G]
    [MulAction G X] [FaithfulSMul G X]
    (horb : ∀ x : X, (MulAction.orbit G x).Finite ∧ (MulAction.orbit G x).ncard ≤ 2) :
    Nat.card G ≤ 2 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := G)
  have hsq : a ^ 2 = 1 :=
    FaithfulSMul.eq_of_smul_eq_smul (α := X)
      (fun x => by rw [sq_smul_eq_self_of_orbit_le_two horb a x, one_smul])
  have hord : orderOf a ≤ 2 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hsq)
  have hcard : Nat.card G = orderOf a := (orderOf_eq_card_of_forall_mem_zpowers ha).symm
  omega

end GaloisForLFunctions.HTGeometry
