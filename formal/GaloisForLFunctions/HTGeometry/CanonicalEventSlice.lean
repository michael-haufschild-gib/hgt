import Mathlib.Order.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Preorder.Finite

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

/-- An inclusion-maximal causal antichain. -/
def IsMaximalCausalAntichain (s : Set α) : Prop :=
  CausalAntichain s ∧
    ∀ ⦃t : Set α⦄, CausalAntichain t → s ⊆ t → t = s

/-- There is exactly one inclusion-maximal causal antichain containing `x`. -/
def UniqueMaximalCausalAntichainAt (x : α) : Prop :=
  ∃! s : Set α, x ∈ s ∧ IsMaximalCausalAntichain s

/-- Every causal antichain in a finite causal order extends to an inclusion-maximal one. -/
theorem exists_maximalCausalAntichain_superset [Fintype α]
    (s : Set α) (hs : CausalAntichain s) :
    ∃ t : Set α, IsMaximalCausalAntichain t ∧ s ⊆ t := by
  classical
  let fs : Finset α := Finset.univ.filter (fun a => a ∈ s)
  have hfs : (fs : Set α) = s := by
    ext a
    simp [fs]
  let candidates : Finset (Finset α) :=
    Finset.univ.powerset.filter (fun t =>
      CausalAntichain (t : Set α) ∧ s ⊆ (t : Set α))
  have hfs_mem : fs ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    rw [hfs]
    exact ⟨hs, Set.Subset.rfl⟩
  obtain ⟨t, hfst, htmax⟩ := candidates.exists_le_maximal hfs_mem
  refine ⟨(t : Set α), ?_, ?_⟩
  · refine ⟨(Finset.mem_filter.mp htmax.1).2.1, ?_⟩
    intro u hu htu
    let fu : Finset α := Finset.univ.filter (fun a => a ∈ u)
    have hfu : (fu : Set α) = u := by
      ext a
      simp [fu]
    have hfu_mem : fu ∈ candidates := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
      rw [hfu]
      exact ⟨hu, (Finset.mem_filter.mp htmax.1).2.2 |>.trans htu⟩
    have htfu : t ⊆ fu := by
      intro a ha
      have hau : a ∈ u := htu ha
      simpa [fu] using hau
    have hfut : fu ⊆ t := htmax.2 hfu_mem htfu
    apply Set.Subset.antisymm
    · intro a ha
      apply hfut
      simpa [fu] using ha
    · exact htu
  · intro a ha
    apply hfst
    simpa [fs] using ha

/-- A greatest slice is inclusion-maximal among all causal antichains. -/
theorem IsGreatestCausalSliceAt.isMaximalCausalAntichain
    {x : α} {s : Set α} (hs : IsGreatestCausalSliceAt x s) :
    IsMaximalCausalAntichain s := by
  refine ⟨hs.2.1, ?_⟩
  intro t ht hst
  apply Set.Subset.antisymm
  · exact hs.antichain_subset (hst hs.1) ht
  · exact hst

/-- Greatest slices force unique maximal-antichain membership at every event. -/
theorem uniqueMaximalCausalAntichains_of_greatestCausalSlices
    (h : ∃ S : α → Set α, ∀ x, IsGreatestCausalSliceAt x (S x)) :
    ∀ x : α, UniqueMaximalCausalAntichainAt x := by
  rcases h with ⟨S, hS⟩
  intro x
  refine ⟨S x, ⟨(hS x).1, (hS x).isMaximalCausalAntichain⟩, ?_⟩
  intro t ht
  exact
    (ht.2.2 (hS x).2.1 ((hS x).antichain_subset ht.1 ht.2.1)).symm

/-- In a finite causal order, unique maximal-antichain membership forces transitive incomparability. -/
theorem augmentedIncomparable_transitive_of_uniqueMaximalCausalAntichains
    [Fintype α]
    (h : ∀ x : α, UniqueMaximalCausalAntichainAt x) :
    AugmentedIncomparableTransitive (α := α) := by
  intro x y z hxy hyz
  obtain ⟨a, ha, hpaira⟩ :=
    exists_maximalCausalAntichain_superset ({x, y} : Set α)
      (causalAntichain_pair_of_augmentedIncomparable hxy)
  obtain ⟨b, hb, hpairb⟩ :=
    exists_maximalCausalAntichain_superset ({y, z} : Set α)
      (causalAntichain_pair_of_augmentedIncomparable hyz)
  have hxa : x ∈ a := hpaira (by simp)
  have hya : y ∈ a := hpaira (by simp)
  have hyb : y ∈ b := hpairb (by simp)
  have hzb : z ∈ b := hpairb (by simp)
  obtain ⟨m, hm, huniq⟩ := h y
  have ham : a = m := huniq a ⟨hya, ha⟩
  have hbm : b = m := huniq b ⟨hyb, hb⟩
  have hza : z ∈ a := by
    rw [ham, ← hbm]
    exact hzb
  exact ha.1 hxa hza

/-- Finite unique-maximal-antichain membership is equivalent to the weak-order condition. -/
theorem finite_uniqueMaximalCausalAntichains_iff_augmentedIncomparable_transitive
    [Fintype α] :
    (∀ x : α, UniqueMaximalCausalAntichainAt x) ↔
      AugmentedIncomparableTransitive (α := α) := by
  constructor
  · exact augmentedIncomparable_transitive_of_uniqueMaximalCausalAntichains
  · intro htrans
    apply uniqueMaximalCausalAntichains_of_greatestCausalSlices
    exact greatestCausalSlices_iff_augmentedIncomparable_transitive.mpr htrans

/-- Under the weak-order condition, augmented incomparability is an equivalence relation. -/
theorem augmentedIncomparable_equivalence
    (htrans : AugmentedIncomparableTransitive (α := α)) :
    Equivalence (augmentedIncomparable (α := α)) :=
  ⟨augmentedIncomparable_refl,
    fun {_} {_} h => augmentedIncomparable_symm h,
    fun {_} {_} {_} hxy hyz => htrans hxy hyz⟩

/-- Each canonical equivalence class is a causal antichain. -/
theorem canonicalCausalSlice_causalAntichain
    (htrans : AugmentedIncomparableTransitive (α := α)) (x : α) :
    CausalAntichain (canonicalCausalSlice x) :=
  (canonicalCausalSlice_isGreatest htrans x).2.1

/-- Every greatest slice is exactly the canonical augmented-incomparability class. -/
theorem greatestCausalSliceAt_eq_canonical
    (htrans : AugmentedIncomparableTransitive (α := α))
    {x : α} {s : Set α} (hs : IsGreatestCausalSliceAt x s) :
    s = canonicalCausalSlice x :=
  greatestCausalSliceAt_unique hs (canonicalCausalSlice_isGreatest htrans x)

/-- Strict comparison is independent of the chosen representatives of two canonical classes. -/
theorem lt_of_augmentedIncomparable_of_lt_of_augmentedIncomparable
    (htrans : AugmentedIncomparableTransitive (α := α))
    {x x' y y' : α}
    (hxx' : augmentedIncomparable x x') (hxy : x < y)
    (hyy' : augmentedIncomparable y y') : x' < y' := by
  have hx'y : x' < y := by
    have hnot : ¬ augmentedIncomparable x' y := by
      intro h
      exact (htrans hxx' h).1 hxy
    rcases lt_or_gt_of_not_augmentedIncomparable hnot with h | h
    · exact h
    · exact (hxx'.1 (lt_trans hxy h)).elim
  have hnot : ¬ augmentedIncomparable x' y' := by
    intro h
    exact (htrans h (augmentedIncomparable_symm hyy')).1 hx'y
  rcases lt_or_gt_of_not_augmentedIncomparable hnot with h | h
  · exact h
  · exact (hyy'.2 (lt_trans h hx'y)).elim

/-- Strict comparison of canonical slices is independent of their representatives. -/
theorem canonicalCausalSlice_lt_wellDefined
    (htrans : AugmentedIncomparableTransitive (α := α))
    {x x' y y' : α}
    (hxx' : canonicalCausalSlice x = canonicalCausalSlice x')
    (hxy : x < y)
    (hyy' : canonicalCausalSlice y = canonicalCausalSlice y') : x' < y' :=
  lt_of_augmentedIncomparable_of_lt_of_augmentedIncomparable htrans
    (canonicalCausalSlice_eq_iff htrans |>.mp hxx') hxy
    (canonicalCausalSlice_eq_iff htrans |>.mp hyy')

/-- Two canonical classes are equal, or else are strictly comparable in one unique direction. -/
theorem canonicalCausalSlice_eq_or_lt_or_gt
    (htrans : AugmentedIncomparableTransitive (α := α))
    (x y : α) :
    canonicalCausalSlice x = canonicalCausalSlice y ∨ x < y ∨ y < x := by
  by_cases hxy : canonicalCausalSlice x = canonicalCausalSlice y
  · exact Or.inl hxy
  · right
    apply lt_or_gt_of_not_augmentedIncomparable
    intro h
    exact hxy ((canonicalCausalSlice_eq_iff htrans).mpr h)

end GaloisForLFunctions.HTGeometry
