import GaloisForLFunctions.RHTower.Sieve.MaynardGreedyGrouping
import GaloisForLFunctions.RHTower.Sieve.MaynardGroupSelection

/-!
# Selecting a large group from the robust greedy partition

This module combines the new `[t,4t)` partition with the multiplicative pigeonhole.  The output is
one literal finset group, and then its finite subtype, with both its additive mass window and its
exact multiplicative large-value threshold.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

@[simp] theorem mem_foldr_union_iff {ι : Type*} [DecidableEq ι]
    (i : ι) (groups : List (Finset ι)) :
    i ∈ groups.foldr (· ∪ ·) ∅ ↔ ∃ u ∈ groups, i ∈ u := by
  induction groups with
  | nil => simp
  | cons u groups ih => simp [ih]

/-- Product over pairwise-disjoint groups equals the product over their union. -/
theorem list_prod_group_products_eq_union
    {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (f : ι → M) (groups : List (Finset ι))
    (hpair : groups.Pairwise Disjoint) :
    (groups.map fun u => ∏ i ∈ u, f i).prod =
      ∏ i ∈ groups.foldr (· ∪ ·) ∅, f i := by
  induction groups with
  | nil => simp
  | cons u groups ih =>
      obtain ⟨hdis, hpair'⟩ := List.pairwise_cons.mp hpair
      have hu : Disjoint u (groups.foldr (· ∪ ·) ∅) := by
        rw [Finset.disjoint_left]
        intro i hiu hiunion
        obtain ⟨v, hv, hiv⟩ := (mem_foldr_union_iff i groups).mp hiunion
        exact (Finset.disjoint_left.mp (hdis v hv)) hiu hiv
      simp only [List.map_cons, List.prod_cons, List.foldr_cons]
      rw [ih hpair', Finset.prod_union hu]

/-- Product over the `Fin length` indexing of a group list. -/
theorem fin_prod_group_get_eq_list_prod
    {ι M : Type*} [CommMonoid M] (groups : List ι) (f : ι → M) :
    (∏ j : Fin groups.length, f (groups.get j)) = (groups.map f).prod := by
  rw [← List.prod_ofFn]
  simp

/-- A packing of a family with mass at least a positive threshold has at least one group. -/
theorem greedyWeightPacking_ne_nil
    {ι : Type*} [DecidableEq ι] {w : ι → ℝ} {t : ℝ} {s : Finset ι}
    {groups : List (Finset ι)} (ht : 0 < t)
    (htotal : t ≤ ∑ i ∈ s, w i)
    (hpacking : IsGreedyWeightPacking w t s groups) : groups ≠ [] := by
  intro hnil
  subst groups
  have hs : s = ∅ := by simpa [IsGreedyWeightPacking] using hpacking.2.2.symm
  subst s
  simp at htotal
  linarith

/-- One member of a fixed robust packing inherits the multiplicative large-value threshold. -/
theorem exists_large_group_mem_packing
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t : ℝ) (s : Finset ι) (groups : List (Finset ι))
    (ht : 0 < t) (htotal : t ≤ ∑ i ∈ s, w i)
    (hpacking : IsGreedyWeightPacking w t s groups)
    (A : ι → ℝ) (z : ι → ℂ) (e : ℝ)
    (hA : ∀ i ∈ s, 0 < A i)
    (hlarge : (∏ i ∈ s, A i) ^ e ≤ ‖∏ i ∈ s, z i‖) :
    ∃ u ∈ groups, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < 4 * t ∧
      (∏ i ∈ u, A i) ^ e ≤ ‖∏ i ∈ u, z i‖ := by
  classical
  have hne := greedyWeightPacking_ne_nil ht htotal hpacking
  have hlen : 0 < groups.length := List.length_pos_of_ne_nil hne
  letI : Nonempty (Fin groups.length) := ⟨⟨0, hlen⟩⟩
  let groupA : Fin groups.length → ℝ := fun j => ∏ i ∈ groups.get j, A i
  let groupV : Fin groups.length → ℝ := fun j => ‖∏ i ∈ groups.get j, z i‖
  have hgroupA : ∀ j, 0 < groupA j := by
    intro j
    apply Finset.prod_pos
    intro i hi
    exact hA i ((hpacking.2.1 (groups.get j) (List.get_mem groups j)).2.1 hi)
  have hprodA : ∏ j, groupA j = ∏ i ∈ s, A i := by
    rw [show (∏ j, groupA j) =
      (groups.map fun u => ∏ i ∈ u, A i).prod by
        exact fin_prod_group_get_eq_list_prod groups (fun u => ∏ i ∈ u, A i)]
    rw [list_prod_group_products_eq_union A groups hpacking.1, hpacking.2.2]
  have hprodZ : ∏ j, groupV j = ‖∏ i ∈ s, z i‖ := by
    calc
      ∏ j, groupV j = ‖∏ j, ∏ i ∈ groups.get j, z i‖ := by
        rw [Complex.norm_prod]
      _ = ‖(groups.map fun u => ∏ i ∈ u, z i).prod‖ := by
        exact congrArg norm
          (fin_prod_group_get_eq_list_prod groups (fun u => ∏ i ∈ u, z i))
      _ = ‖∏ i ∈ groups.foldr (· ∪ ·) ∅, z i‖ := by
        rw [list_prod_group_products_eq_union z groups hpacking.1]
      _ = ‖∏ i ∈ s, z i‖ := by rw [hpacking.2.2]
  have hselected := exists_rpow_le_of_prod_rpow_le_prod
    groupA groupV e hgroupA (fun j => norm_nonneg _)
    (show (∏ j, groupA j) ^ e ≤ ∏ j, groupV j by rw [hprodA, hprodZ]; exact hlarge)
  obtain ⟨j, hj⟩ := hselected
  let u := groups.get j
  have hu : u ∈ groups := List.get_mem groups j
  obtain ⟨hune, hus, hulower, huupper⟩ := hpacking.2.1 u hu
  exact ⟨u, hu, hune, hus, hulower, huupper, hj⟩

/-- **Robust greedy large-group theorem.**  The grouping and large-value selection are both
constructed: no partition or exponent-selection premise remains. -/
theorem exists_robust_greedy_large_group
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t : ℝ) (s : Finset ι)
    (ht : 0 < t) (hw2 : ∀ i ∈ s, w i ≤ 2 * t)
    (htotal : t ≤ ∑ i ∈ s, w i)
    (A : ι → ℝ) (z : ι → ℂ) (e : ℝ)
    (hA : ∀ i ∈ s, 0 < A i)
    (hlarge : (∏ i ∈ s, A i) ^ e ≤ ‖∏ i ∈ s, z i‖) :
    ∃ u : Finset ι, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < 4 * t ∧
      (∏ i ∈ u, A i) ^ e ≤ ‖∏ i ∈ u, z i‖ := by
  obtain ⟨groups, hpacking⟩ := exists_greedy_weight_packing w t s ht hw2 htotal
  obtain ⟨u, _hu, hune, hus, hulower, huupper, hgroup⟩ :=
    exists_large_group_mem_packing w t s groups ht htotal hpacking A z e hA hlarge
  exact ⟨u, hune, hus, hulower, huupper, hgroup⟩

/-- Subtype form consumed by the literal grouped-factor Huxley theorem. -/
theorem exists_robust_greedy_large_group_subtype
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t : ℝ) (s : Finset ι)
    (ht : 0 < t) (hw2 : ∀ i ∈ s, w i ≤ 2 * t)
    (htotal : t ≤ ∑ i ∈ s, w i)
    (A : ι → ℝ) (z : ι → ℂ) (e : ℝ)
    (hA : ∀ i ∈ s, 0 < A i)
    (hlarge : (∏ i ∈ s, A i) ^ e ≤ ‖∏ i ∈ s, z i‖) :
    ∃ u : Finset ι, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < 4 * t ∧
      (∏ i : {i // i ∈ u}, A i) ^ e ≤ ‖∏ i : {i // i ∈ u}, z i‖ := by
  obtain ⟨u, hune, hus, hulower, huupper, hgroup⟩ :=
    exists_robust_greedy_large_group w t s ht hw2 htotal A z e hA hlarge
  refine ⟨u, hune, hus, hulower, huupper, ?_⟩
  simpa only [← Finset.prod_subtype u (fun _ => Iff.rfl)] using hgroup

end RHTower.Sieve
