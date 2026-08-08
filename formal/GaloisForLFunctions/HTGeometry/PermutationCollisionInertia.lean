import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.Set.Card

/-!
# Permutations preserving a unique collision

At a simple branch value, all sheets have distinct reductions except the two branches of one fold.
Any inertia permutation preserves reduction, hence its support is contained in those two colliding
sheets.  This module isolates that exact finite permutation argument.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv

universe u v

/-- Points whose label is shared by a distinct point. -/
def collisionSupport {α : Type u} {β : Type v} (r : α → β) : Set α :=
  {x | ∃ y, y ≠ x ∧ r y = r x}

/-- A permutation preserving a label map can move only points in the collision support. -/
theorem permSupport_subset_collisionSupport
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    (r : α → β) (σ : Equiv.Perm α) (hσ : ∀ x, r (σ x) = r x) :
    (↑σ.support : Set α) ⊆ collisionSupport r := by
  intro x hx
  exact ⟨σ x, Equiv.Perm.mem_support.mp hx, hσ x⟩

/-- **Unique-collision inertia criterion.**  If at most two points share any label with another
point, every label-preserving permutation is the identity or a single transposition. -/
theorem eq_one_or_isSwap_of_collisionSupport_ncard_le_two
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    (r : α → β) (hcard : (collisionSupport r).ncard ≤ 2)
    (σ : Equiv.Perm α) (hσ : ∀ x, r (σ x) = r x) :
    σ = 1 ∨ σ.IsSwap := by
  by_cases htrivial : σ = 1
  · exact Or.inl htrivial
  · right
    have hsupport : (↑σ.support : Set α) ⊆ collisionSupport r :=
      permSupport_subset_collisionSupport r σ hσ
    have hle : σ.support.card ≤ (collisionSupport r).ncard := by
      simpa using Set.ncard_le_ncard hsupport
    rw [← Equiv.Perm.card_support_eq_two]
    exact le_antisymm (hle.trans hcard)
      (Equiv.Perm.two_le_card_support_of_ne_one htrivial)

/-- A group action preserving a label map has only trivial elements and transpositions when the
whole collision support has cardinality at most two. -/
theorem permAction_eq_one_or_isSwap_of_collisionSupport_ncard_le_two
    {G : Type*} [Group G] {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] (ρ : G →* Equiv.Perm α)
    (r : α → β) (hcard : (collisionSupport r).ncard ≤ 2)
    (hinvariant : ∀ g x, r (ρ g x) = r x) (g : G) :
    ρ g = 1 ∨ (ρ g).IsSwap :=
  eq_one_or_isSwap_of_collisionSupport_ncard_le_two r hcard (ρ g) (hinvariant g)

end GaloisForLFunctions.HTGeometry
