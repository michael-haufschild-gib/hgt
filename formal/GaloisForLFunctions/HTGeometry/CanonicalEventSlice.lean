import Mathlib.Order.Basic
import Mathlib.Data.Set.Lattice

/-!
# Canonical event slices and weak-order collapse

For a partial order, call two events augmented-incomparable when neither is strictly before the
other. A greatest causal slice through an event is an antichain containing every event
augmented-incomparable with it.

Every event admits such a greatest slice exactly when augmented incomparability is transitive.
In that case the slices are precisely the augmented-incomparability classes, so the partial order
is a strict weak order: an ordinal stack of antichains.

This is elementary order-theoretic infrastructure. Its physical use is a no-go boundary:
causal order alone can canonically complete every event to one spatial slice only by collapsing
to absolute ordered simultaneity layers.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [PartialOrder α]

/-- Equality-or-incomparability for the strict relation of a partial order. -/
def augmentedIncomparable (x y : α) : Prop :=
  ¬ x < y ∧ ¬ y < x

@[simp]
theorem augmentedIncomparable_refl (x : α) :
    augmentedIncomparable x x :=
  ⟨lt_irrefl x, lt_irrefl x⟩

theorem augmentedIncomparable_symm {x y : α}
    (h : augmentedIncomparable x y) :
    augmentedIncomparable y x :=
  ⟨h.2, h.1⟩

/-- Transitivity of equality-or-incomparability. -/
def AugmentedIncomparableTransitive : Prop :=
  ∀ ⦃x y z : α⦄,
    augmentedIncomparable x y →
      augmentedIncomparable y z →
        augmentedIncomparable x z

/-- A causal antichain: every pair is equal or incomparable. -/
def CausalAntichain (s : Set α) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ s → y ∈ s → augmentedIncomparable x y

/-- A pair of equal-or-incomparable events is a causal antichain. -/
theorem causalAntichain_pair_of_augmentedIncomparable
    {x y : α} (hxy : augmentedIncomparable x y) :
    CausalAntichain ({x, y} : Set α) := by
  intro a b ha hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with ha | ha
  · subst a
    rcases hb with hb | hb
    · subst b
      exact augmentedIncomparable_refl _
    · subst b
      exact hxy
  · subst a
    rcases hb with hb | hb
    · subst b
      exact augmentedIncomparable_symm hxy
    · subst b
      exact augmentedIncomparable_refl _

/--
A greatest causal slice through `x`: an antichain containing `x` and every event
equal or incomparable to `x`.
-/
def IsGreatestCausalSliceAt (x : α) (s : Set α) : Prop :=
  x ∈ s ∧
    CausalAntichain s ∧
      ∀ ⦃y : α⦄, augmentedIncomparable x y → y ∈ s

/-- Order-theoretic formulation: every antichain through `x` is contained in `s`. -/
def IsOrderGreatestCausalSliceAt (x : α) (s : Set α) : Prop :=
  x ∈ s ∧
    CausalAntichain s ∧
      ∀ t : Set α, x ∈ t → CausalAntichain t → t ⊆ s

theorem IsGreatestCausalSliceAt.mem_iff
    {x y : α} {s : Set α}
    (h : IsGreatestCausalSliceAt x s) :
    y ∈ s ↔ augmentedIncomparable x y := by
  constructor
  · intro hy
    exact h.2.1 h.1 hy
  · intro hxy
    exact h.2.2 hxy

/-- Every antichain through `x` lies in a greatest causal slice through `x`. -/
theorem IsGreatestCausalSliceAt.antichain_subset
    {x : α} {s t : Set α}
    (hs : IsGreatestCausalSliceAt x s)
    (hxt : x ∈ t) (ht : CausalAntichain t) :
    t ⊆ s := by
  intro y hy
  exact hs.2.2 (ht hxt hy)

theorem IsGreatestCausalSliceAt.isOrderGreatest
    {x : α} {s : Set α}
    (hs : IsGreatestCausalSliceAt x s) :
    IsOrderGreatestCausalSliceAt x s :=
  ⟨hs.1, hs.2.1, fun _ hxt ht => hs.antichain_subset hxt ht⟩

theorem IsOrderGreatestCausalSliceAt.isGreatest
    {x : α} {s : Set α}
    (hs : IsOrderGreatestCausalSliceAt x s) :
    IsGreatestCausalSliceAt x s := by
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro y hxy
  have hpair : CausalAntichain ({x, y} : Set α) :=
    causalAntichain_pair_of_augmentedIncomparable hxy
  exact hs.2.2 ({x, y} : Set α) (by simp) hpair (by simp)

/-- Greatest causal slices through the same event are unique. -/
theorem greatestCausalSliceAt_unique
    {x : α} {s t : Set α}
    (hs : IsGreatestCausalSliceAt x s)
    (ht : IsGreatestCausalSliceAt x t) :
    s = t := by
  apply Set.ext
  intro y
  rw [hs.mem_iff, ht.mem_iff]

/-- The canonical candidate slice through an event. -/
def canonicalCausalSlice (x : α) : Set α :=
  {y | augmentedIncomparable x y}

@[simp]
theorem mem_canonicalCausalSlice_iff {x y : α} :
    y ∈ canonicalCausalSlice x ↔ augmentedIncomparable x y :=
  Iff.rfl

/--
Transitive augmented incomparability makes the canonical candidate a greatest
antichain through every event.
-/
theorem canonicalCausalSlice_isGreatest
    (htrans : AugmentedIncomparableTransitive (α := α))
    (x : α) :
    IsGreatestCausalSliceAt x (canonicalCausalSlice x) := by
  refine ⟨augmentedIncomparable_refl x, ?_, ?_⟩
  · intro y z hy hz
    exact htrans (augmentedIncomparable_symm hy) hz
  · intro y hy
    exact hy

/--
Every event has a greatest causal slice exactly when augmented incomparability
is transitive. This is the strict-weak-order collapse behind canonical slicing.
-/
theorem greatestCausalSlices_iff_augmentedIncomparable_transitive :
    (∃ S : α → Set α, ∀ x, IsGreatestCausalSliceAt x (S x)) ↔
      AugmentedIncomparableTransitive (α := α) := by
  constructor
  · rintro ⟨S, hS⟩ x y z hxy hyz
    have hx : x ∈ S y :=
      (hS y).2.2 (augmentedIncomparable_symm hxy)
    have hz : z ∈ S y :=
      (hS y).2.2 hyz
    exact (hS y).2.1 hx hz
  · intro htrans
    exact ⟨canonicalCausalSlice,
      fun x => canonicalCausalSlice_isGreatest htrans x⟩

/--
Exact order-theoretic form: every event belongs to a greatest antichain exactly
when augmented incomparability is transitive.
-/
theorem orderGreatestCausalSlices_iff_augmentedIncomparable_transitive :
    (∃ S : α → Set α, ∀ x, IsOrderGreatestCausalSliceAt x (S x)) ↔
      AugmentedIncomparableTransitive (α := α) := by
  constructor
  · rintro ⟨S, hS⟩
    rw [← greatestCausalSlices_iff_augmentedIncomparable_transitive]
    exact ⟨S, fun x => (hS x).isGreatest⟩
  · intro htrans
    exact ⟨canonicalCausalSlice,
      fun x => (canonicalCausalSlice_isGreatest htrans x).isOrderGreatest⟩

/--
Under the weak-order condition, two events determine the same canonical slice
exactly when they are equal or incomparable.
-/
theorem canonicalCausalSlice_eq_iff
    (htrans : AugmentedIncomparableTransitive (α := α))
    {x y : α} :
    canonicalCausalSlice x = canonicalCausalSlice y ↔
      augmentedIncomparable x y := by
  constructor
  · intro hxy
    have hy : y ∈ canonicalCausalSlice y :=
      augmentedIncomparable_refl y
    rw [← hxy] at hy
    exact hy
  · intro hxy
    apply Set.ext
    intro z
    constructor
    · intro hxz
      exact htrans (augmentedIncomparable_symm hxy) hxz
    · intro hyz
      exact htrans hxy hyz

/-- Events outside one augmented-incomparability class are strictly comparable. -/
theorem lt_or_gt_of_not_augmentedIncomparable
    {x y : α} (h : ¬ augmentedIncomparable x y) :
    x < y ∨ y < x := by
  by_cases hxy : x < y
  · exact Or.inl hxy
  · right
    by_contra hyx
    exact h ⟨hxy, hyx⟩

end GaloisForLFunctions.HTGeometry
