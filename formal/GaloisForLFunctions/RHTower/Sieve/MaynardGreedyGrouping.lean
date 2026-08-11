import GaloisForLFunctions.RHTower.Sieve.MaynardAllShortHuxley
import Mathlib.Data.Finset.Powerset

/-!
# Robust greedy grouping for Maynard factors

The exact three-threshold packing convention is unnecessarily brittle.  Minimal heavy subsets have
mass in `[t,3t)`.  Repeating this extraction and merging the final sub-threshold remainder produces
a genuine partition into groups of mass `[t,4t)`.  Together with the widened exponent audit in
`MaynardAllShortHuxley`, this is sufficient and retains a positive `73/1440` ambient reserve.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- A list of finsets is a robust threshold packing of `s` for weight `w`. -/
def IsGreedyWeightPacking {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t : ℝ) (s : Finset ι) (groups : List (Finset ι)) : Prop :=
  groups.Pairwise Disjoint ∧
    (∀ u ∈ groups, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < 4 * t) ∧
    groups.foldr (· ∪ ·) ∅ = s

/-- A finite family with total mass at least `t` and atoms at most `2t` contains a nonempty
minimal heavy subset of mass in `[t,3t)`. -/
theorem exists_minimal_weight_group
    {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (t : ℝ) (s : Finset ι)
    (ht : 0 < t) (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw2 : ∀ i ∈ s, w i ≤ 2 * t)
    (htotal : t ≤ ∑ i ∈ s, w i) :
    ∃ u : Finset ι, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < 3 * t := by
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
  have hiS : i ∈ s := huinfo.1 hi
  have hiupper := hw2 i hiS
  have hsum := Finset.sum_erase_add u w hi
  refine ⟨u, hune, huinfo.1, huinfo.2, ?_⟩
  linarith

/-- **Robust greedy partition.**  Repeated minimal-heavy extraction partitions every finite family
of nonnegative atoms of size at most `2t` and total mass at least `t` into groups with mass in
`[t,4t)`.  The terminal factor `4` occurs only when the final light remainder is merged. -/
theorem exists_greedy_weight_packing
    {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (t : ℝ) (s : Finset ι)
    (ht : 0 < t) (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw2 : ∀ i ∈ s, w i ≤ 2 * t)
    (htotal : t ≤ ∑ i ∈ s, w i) :
    ∃ groups : List (Finset ι), IsGreedyWeightPacking w t s groups := by
  classical
  induction s using Finset.strongInductionOn with
  | h s ih =>
      obtain ⟨u, hune, hus, hulower, huupper⟩ :=
        exists_minimal_weight_group w t s ht hw0 hw2 htotal
      let r : Finset ι := s \ u
      have hrs : r ⊆ s := Finset.sdiff_subset
      have hur : Disjoint u r := by
        dsimp [r]
        exact Finset.disjoint_sdiff
      by_cases hrtotal : t ≤ ∑ i ∈ r, w i
      · have hrproper : r ⊂ s := by
          dsimp [r]
          exact Finset.sdiff_ssubset hus hune
        have hrw0 : ∀ i ∈ r, 0 ≤ w i := fun i hi => hw0 i (hrs hi)
        have hrw2 : ∀ i ∈ r, w i ≤ 2 * t := fun i hi => hw2 i (hrs hi)
        obtain ⟨groups, hpair, hgroups, hcover⟩ :=
          ih r hrproper hrw0 hrw2 hrtotal
        refine ⟨u :: groups, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨?_, hpair⟩
          intro v hv
          have hvsub : v ⊆ r := (hgroups v hv).2.1
          exact hur.mono_right hvsub
        · intro v hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact ⟨hune, hus, hulower, huupper.trans_le (by linarith)⟩
          · obtain ⟨hvne, hvr, hvlower, hvupper⟩ := hgroups v hv
            exact ⟨hvne, hvr.trans hrs, hvlower, hvupper⟩
        · simp only [List.foldr_cons]
          rw [hcover]
          dsimp [r]
          ext i
          simp only [Finset.mem_union, Finset.mem_sdiff]
          constructor
          · rintro (hiu | ⟨his, _⟩)
            · exact hus hiu
            · exact his
          · intro his
            by_cases hiu : i ∈ u
            · exact Or.inl hiu
            · exact Or.inr ⟨his, hiu⟩
      · have hrupper : (∑ i ∈ r, w i) < t := lt_of_not_ge hrtotal
        have hdecomp := Finset.sum_sdiff hus (f := w)
        have hsupper : (∑ i ∈ s, w i) < 4 * t := by
          dsimp [r] at hrupper
          linarith
        refine ⟨[s], ?_⟩
        simp [IsGreedyWeightPacking, htotal, hsupper]

end RHTower.Sieve
