import GaloisForLFunctions.RHTower.Sieve.MaynardBoundedGreedyGrouping

/-!
# Minimal-group witnesses in sub-height packing

An overweight cell produced by minimal-threshold greedy packing is never diffuse.  Removing one
distinguished atom leaves mass below the threshold.  Consequently every cell whose mass reaches
the height cap contains an atom within two thresholds of that cap.  This is the combinatorial link
from overweight selected polynomials to adaptive low-order derivative control.
-/

noncomputable section
namespace RHTower.Sieve

open Finset

/-- A bounded packing together with the near-cap atom forced in every overweight cell. -/
def IsWitnessedBoundedWeightPacking {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t B : ℝ) (s : Finset ι)
    (groups : List (Finset ι)) : Prop :=
  IsBoundedWeightPacking w t B s groups ∧
    ∀ u ∈ groups, ∃ i ∈ u,
      (∑ j ∈ u, w j) - 2 * t < w i

/-- A minimal threshold-heavy group contains an atom larger than its total mass minus `t`. -/
theorem exists_minimal_bounded_weight_group_with_atom
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t B : ℝ) (s : Finset ι)
    (ht : 0 < t) (hwB : ∀ i ∈ s, w i ≤ B)
    (htotal : t ≤ ∑ i ∈ s, w i) :
    ∃ u : Finset ι, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < t + B ∧
      ∃ i ∈ u, (∑ j ∈ u, w j) - t < w i := by
  classical
  let candidates : Finset (Finset ι) :=
    s.powerset.filter fun u => t ≤ ∑ i ∈ u, w i
  have hcandidates : candidates.Nonempty := by
    refine ⟨s, ?_⟩
    simp [candidates, htotal]
  obtain ⟨u, hu, hmin⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have huinfo : u ⊆ s ∧ t ≤ ∑ i ∈ u, w i := by
    simpa [candidates] using hu
  have hune : u.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro huzero
    subst u
    simp at huinfo
    linarith
  obtain ⟨i, hi⟩ := hune
  have herase_not : u.erase i ∉ candidates := by
    intro herase
    have hcardmin := hmin (u.erase i) herase
    have hcardlt := Finset.card_lt_card (Finset.erase_ssubset hi)
    omega
  have herase_sub : u.erase i ⊆ s :=
    (Finset.erase_subset i u).trans huinfo.1
  have herase_lt : (∑ j ∈ u.erase i, w j) < t := by
    apply lt_of_not_ge
    intro herase_ge
    apply herase_not
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨herase_sub, herase_ge⟩
  have hiupper := hwB i (huinfo.1 hi)
  have hsum := Finset.sum_erase_add u w hi
  refine ⟨u, ⟨i, hi⟩, huinfo.1, huinfo.2, ?_, i, hi, ?_⟩ <;> linarith

/-- **Witnessed greedy packing.**  Every cap-reaching output cell contains a near-cap atom. -/
theorem exists_witnessed_bounded_weight_packing
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t B : ℝ) (s : Finset ι)
    (ht : 0 < t) (hwB : ∀ i ∈ s, w i ≤ B)
    (htotal : t ≤ ∑ i ∈ s, w i) :
    ∃ groups : List (Finset ι),
      IsWitnessedBoundedWeightPacking w t B s groups := by
  classical
  revert hwB htotal
  refine Finset.strongInduction (p := fun s =>
    (∀ i ∈ s, w i ≤ B) → t ≤ ∑ i ∈ s, w i →
      ∃ groups : List (Finset ι),
        IsWitnessedBoundedWeightPacking w t B s groups) ?_ s
  intro s ih hwB htotal
  obtain ⟨u, hune, hus, hulower, huupper, i, hi, hiweight⟩ :=
    exists_minimal_bounded_weight_group_with_atom w t B s ht hwB htotal
  let r : Finset ι := s \ u
  have hrs : r ⊆ s := Finset.sdiff_subset
  have hur : Disjoint u r := by
    dsimp [r]
    exact Finset.disjoint_sdiff
  by_cases hrtotal : t ≤ ∑ i ∈ r, w i
  · have hrproper : r ⊂ s := by
      dsimp [r]
      exact Finset.sdiff_ssubset hus hune
    have hrwB : ∀ i ∈ r, w i ≤ B := fun i hi => hwB i (hrs hi)
    obtain ⟨groups, hpacking, hwitness⟩ := ih r hrproper hrwB hrtotal
    refine ⟨u :: groups, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hpacking.1⟩
        intro v hv
        have hvsub : v ⊆ r := (hpacking.2.1 v hv).2.1
        exact hur.mono_right hvsub
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact ⟨hune, hus, hulower, huupper.trans_le (by linarith)⟩
        · obtain ⟨hvne, hvr, hvlower, hvupper⟩ := hpacking.2.1 v hv
          exact ⟨hvne, hvr.trans hrs, hvlower, hvupper⟩
      · simp only [List.foldr_cons]
        rw [hpacking.2.2]
        dsimp [r]
        ext j
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (hju | ⟨hjs, _⟩)
          · exact hus hju
          · exact hjs
        · intro hjs
          by_cases hju : j ∈ u
          · exact Or.inl hju
          · exact Or.inr ⟨hjs, hju⟩
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · refine ⟨i, hi, ?_⟩
        linarith
      · exact hwitness v hv
  · have hrupper : (∑ i ∈ r, w i) < t := lt_of_not_ge hrtotal
    have hdecomp := Finset.sum_sdiff hus (f := w)
    have hsupper : (∑ i ∈ s, w i) < B + 2 * t := by
      dsimp [r] at hrupper
      linarith
    have hsne : s.Nonempty := hune.mono hus
    refine ⟨[s], ?_, ?_⟩
    · simp [IsBoundedWeightPacking, hsne, htotal, hsupper]
    · intro v hv
      simp only [List.mem_singleton] at hv
      subst v
      refine ⟨i, hus hi, ?_⟩
      dsimp [r] at hrupper
      linarith

/-- Multiplicative large-group selection preserving the near-cap atom certificate. -/
theorem exists_witnessed_bounded_greedy_large_group
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t B : ℝ) (s : Finset ι)
    (ht : 0 < t) (hwB : ∀ i ∈ s, w i ≤ B)
    (htotal : t ≤ ∑ i ∈ s, w i)
    (A : ι → ℝ) (z : ι → ℂ) (e : ℝ)
    (hA : ∀ i ∈ s, 0 < A i)
    (hlarge : (∏ i ∈ s, A i) ^ e ≤ ‖∏ i ∈ s, z i‖) :
    ∃ u : Finset ι, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < B + 2 * t ∧
      (∏ i ∈ u, A i) ^ e ≤ ‖∏ i ∈ u, z i‖ ∧
      (∃ j ∈ u, (∑ i ∈ u, w i) - 2 * t < w j) ∧
      ((∑ i ∈ u, w i) < B ∨
        ∃ j ∈ u, B - 2 * t < w j) := by
  obtain ⟨groups, hpacking, hwitness⟩ :=
    exists_witnessed_bounded_weight_packing w t B s ht hwB htotal
  obtain ⟨u, _hu, hune, hus, hulower, huupper, hugroup⟩ :=
    exists_large_group_mem_bounded_packing
      w t B s groups ht htotal hpacking A z e hA hlarge
  have hlocal := hwitness u _hu
  refine ⟨u, hune, hus, hulower, huupper, hugroup, hlocal, ?_⟩
  by_cases huB : (∑ i ∈ u, w i) < B
  · exact Or.inl huB
  · obtain ⟨j, hju, hjweight⟩ := hlocal
    exact Or.inr ⟨j, hju, by linarith⟩

end RHTower.Sieve
