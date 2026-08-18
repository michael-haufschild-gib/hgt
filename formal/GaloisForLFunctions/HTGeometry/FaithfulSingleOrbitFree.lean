import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# A single nontrivial orbit of a commutative faithful action is free

If every point of a faithful action is either fixed by the whole group or lies in the orbit of one
distinguished point, and the group is commutative, then that point has trivial stabiliser: an
element fixing it commutes past the translations, so it fixes the whole orbit and hence everything.
The orbit therefore has exactly as many members as the group.

```text
eq_one_of_forall_smul_eq
eq_one_of_smul_eq_of_unique_nontrivial_orbit
    ** one nontrivial orbit + commutative + faithful  ⟹  that orbit is free **
natCard_orbit_eq_natCard_of_free
```

Cyclic groups are commutative, so this is the step that turns "there is only one collision class"
into "the collision class has as many members as the inertia group".
-/

namespace GaloisForLFunctions.HTGeometry

/-- An element acting trivially everywhere is the identity. -/
theorem eq_one_of_forall_smul_eq {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    {g : G} (h : ∀ x : X, g • x = x) : g = 1 :=
  FaithfulSMul.eq_of_smul_eq_smul (α := X) (fun x => by rw [h x, one_smul])

/-- **A single nontrivial orbit of a commutative faithful action is free.**  If every point is
either fixed by the whole group or lies in the orbit of one distinguished point, and the group is
commutative, the stabiliser of that point is trivial. -/
theorem eq_one_of_smul_eq_of_unique_nontrivial_orbit
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    (hcomm : ∀ a b : G, a * b = b * a) {x₀ : X}
    (hcover : ∀ x : X, (∀ g : G, g • x = x) ∨ ∃ h : G, x = h • x₀)
    {g : G} (hg : g • x₀ = x₀) : g = 1 := by
  refine eq_one_of_forall_smul_eq (X := X) fun x => ?_
  rcases hcover x with hfix | ⟨h, rfl⟩
  · exact hfix g
  · rw [smul_smul, hcomm, ← smul_smul, hg]

/-- The orbit of a point with trivial stabiliser has as many members as the group. -/
theorem natCard_orbit_eq_natCard_of_free
    {G X : Type*} [Group G] [MulAction G X] {x₀ : X}
    (hfree : ∀ g : G, g • x₀ = x₀ → g = 1) :
    Nat.card (MulAction.orbit G x₀) = Nat.card G := by
  have hstab : MulAction.stabilizer G x₀ = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => hfree g hg
  have h1 : (MulAction.stabilizer G x₀).index = Nat.card (MulAction.orbit G x₀) :=
    MulAction.index_stabilizer G x₀
  rw [hstab, Subgroup.index_bot] at h1
  exact h1.symm

end GaloisForLFunctions.HTGeometry
