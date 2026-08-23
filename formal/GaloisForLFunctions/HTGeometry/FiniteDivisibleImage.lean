import Mathlib.GroupTheory.Divisible
import Mathlib.GroupTheory.OrderOfElement

/-!
# A finite quotient of a divisible group is trivial

The image of a divisible group under a homomorphism is again divisible, and a finite divisible
group is trivial: every element is an `m`-th power for `m` the order of the group, and `m`-th
powers vanish by Lagrange.
-/

namespace HTGeometry

/-- **A finite divisible group is trivial.** -/
theorem subsingleton_of_rootableBy {G : Type*} [CommGroup G] [Finite G] [RootableBy G ℕ] :
    Subsingleton G := by
  have hm0 : Nat.card G ≠ 0 := Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  refine ⟨fun a b => ?_⟩
  have key : ∀ g : G, g = 1 := by
    intro g
    have hg : (RootableBy.root g (Nat.card G)) ^ (Nat.card G) = g :=
      RootableBy.root_cancel g hm0
    rw [← hg, pow_card_eq_one']
  rw [key a, key b]

/-- **The image of a divisible group under a homomorphism is trivial as soon as it is finite.** -/
theorem range_eq_bot_of_finite_of_rootableBy {G H : Type*} [CommGroup G] [CommGroup H]
    [RootableBy G ℕ] (f : G →* H) [Finite ↥f.range] : f.range = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro _ ⟨y, rfl⟩
  have hm0 : Nat.card ↥f.range ≠ 0 := Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  have hy : (RootableBy.root y (Nat.card ↥f.range)) ^ (Nat.card ↥f.range) = y :=
    RootableBy.root_cancel y hm0
  have hone : (⟨f (RootableBy.root y (Nat.card ↥f.range)),
      ⟨RootableBy.root y (Nat.card ↥f.range), rfl⟩⟩ : ↥f.range) ^ (Nat.card ↥f.range) = 1 :=
    pow_card_eq_one'
  have hval : (f (RootableBy.root y (Nat.card ↥f.range))) ^ (Nat.card ↥f.range) = 1 := by
    have h := congrArg (fun z : ↥f.range => (z : H)) hone
    simpa using h
  rw [Subgroup.mem_bot, ← hy, map_pow, hval]

end HTGeometry
