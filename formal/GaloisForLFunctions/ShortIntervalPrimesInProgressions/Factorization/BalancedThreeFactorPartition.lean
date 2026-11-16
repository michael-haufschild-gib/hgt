import GaloisForLFunctions.ShortIntervalPrimesInProgressions.Factorization.WeightTrichotomy
import GaloisForLFunctions.RHTower.Sieve.MaynardBoundedGreedyGrouping

/-!
# Simultaneous bilinear and trilinear factor grouping

Lemma 6.2 of arXiv:2610.09567 separates a large factor, a large pair of
factors, and a partition into three groups of relative mass in `[1/10,1/2]`.
The first group can be chosen in `[2/5,1/2]`, so the same partition supplies
a balanced bipartition. The proof reuses minimal threshold-heavy subsets.

The statement is homogeneous in the total mass and includes mass zero.
It therefore applies to every finite family of real logarithmic lengths.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

/-- A maximal atom followed by small atoms crosses two fifths before three fifths. -/
private theorem exists_two_fifths_subset {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (s : Finset ι) (S : ℝ) (hS : 0 < S)
    (htotal : factorMass w s = S)
    (hsingle : ∀ i ∈ s, |w i| < 2 * S / 5)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → |w i| + |w j| < 3 * S / 5) :
    ∃ u ⊆ s, factorMass w u ∈ Set.Icc (2 * S / 5) (3 * S / 5) := by
  classical
  have hsne : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    rw [he, factorMass_empty] at htotal
    linarith only [hS, htotal]
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s (fun j => |w j|) hsne
  by_cases hother : ∃ j ∈ s.erase i, S / 5 ≤ |w j|
  · obtain ⟨j, hj, hwj⟩ := hother
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    have hij : i ≠ j := Ne.symm hji
    have hin : i ∉ ({j} : Finset ι) := by
      simpa only [Finset.mem_singleton] using hij
    have hmass : factorMass w {i, j} = |w i| + |w j| := by
      simp only [factorMass, Finset.sum_insert hin, Finset.sum_singleton]
    have hm := hmax j hjs
    have hp := hpair i hi j hjs hij
    refine ⟨{i, j}, Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hjs), ?_⟩
    rw [hmass]
    exact ⟨by linarith only [hm, hwj], hp.le⟩
  · have hcap : ∀ j ∈ s.erase i, |w j| ≤ S / 5 := by
      intro j hj
      exact (lt_of_not_ge (fun h => hother ⟨j, hj, h⟩)).le
    have hrem : factorMass w (s.erase i) + |w i| = S :=
      (Finset.sum_erase_add s (fun j => |w j|) hi).trans htotal
    have htarget : 0 < 2 * S / 5 - |w i| := sub_pos.mpr (hsingle i hi)
    have htotalrem : 2 * S / 5 - |w i| ≤ factorMass w (s.erase i) := by
      linarith only [hrem, hS]
    obtain ⟨u, _, hus, hul, huu⟩ :=
      RHTower.Sieve.exists_minimal_bounded_weight_group
        (fun j => |w j|) (2 * S / 5 - |w i|) (S / 5) (s.erase i)
        htarget hcap htotalrem
    have hin : i ∉ u := by
      intro hiu
      exact (Finset.mem_erase.mp (hus hiu)).1 rfl
    have hmass : factorMass w (insert i u) = |w i| + factorMass w u := by
      exact Finset.sum_insert hin
    refine ⟨insert i u, Finset.insert_subset hi (hus.trans (Finset.erase_subset i s)), ?_⟩
    change 2 * S / 5 - |w i| ≤ factorMass w u at hul
    change factorMass w u < 2 * S / 5 - |w i| + S / 5 at huu
    rw [hmass]
    exact ⟨by linarith only [hul], by linarith only [huu]⟩

/-- Taking the smaller side places a balanced subset below one half. -/
private theorem exists_two_fifths_half_subset {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (s : Finset ι) (S : ℝ) (hS : 0 < S)
    (htotal : factorMass w s = S)
    (hsingle : ∀ i ∈ s, |w i| < 2 * S / 5)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → |w i| + |w j| < 3 * S / 5) :
    ∃ u ⊆ s, factorMass w u ∈ Set.Icc (2 * S / 5) (S / 2) := by
  obtain ⟨u, hus, hul, huu⟩ := exists_two_fifths_subset w s S hS htotal hsingle hpair
  by_cases hhalf : factorMass w u ≤ S / 2
  · exact ⟨u, hus, hul, hhalf⟩
  · have hsum := (factorMass_add_sdiff w hus).trans htotal
    exact ⟨s \ u, Finset.sdiff_subset,
      by linarith only [hsum, huu], by linarith only [hsum, hhalf]⟩

/-- A remainder of mass between one half and three fifths splits at one tenth. -/
private theorem split_remainder_into_two {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (r : Finset ι) (S : ℝ) (hS : 0 < S)
    (hr : factorMass w r ∈ Set.Icc (S / 2) (3 * S / 5))
    (hcap : ∀ i ∈ r, |w i| < 2 * S / 5) :
    ∃ v ⊆ r, factorMass w v ∈ Set.Icc (S / 10) (S / 2) ∧
      factorMass w (r \ v) ∈ Set.Icc (S / 10) (S / 2) := by
  classical
  by_cases hlarge : ∃ i ∈ r, S / 10 ≤ |w i|
  · obtain ⟨i, hi, hwi⟩ := hlarge
    have his : {i} ⊆ r := Finset.singleton_subset_iff.mpr hi
    have hsum := factorMass_add_sdiff w his
    rw [factorMass_singleton] at hsum
    have hu := hcap i hi
    refine ⟨{i}, his, ?_, ?_⟩
    · rw [factorMass_singleton]
      exact ⟨hwi, by linarith only [hu, hS]⟩
    · exact ⟨by linarith only [hsum, hr.1, hu, hS],
        by linarith only [hsum, hr.2, hwi]⟩
  · have hsmall : ∀ i ∈ r, |w i| ≤ S / 10 := fun i hi =>
      (lt_of_not_ge (fun h => hlarge ⟨i, hi, h⟩)).le
    have ht : 0 < S / 10 := by linarith only [hS]
    have htotal : S / 10 ≤ factorMass w r := by linarith only [hr.1, hS]
    obtain ⟨v, _, hvr, hvl, hvu⟩ :=
      RHTower.Sieve.exists_minimal_bounded_weight_group
        (fun i => |w i|) (S / 10) (S / 10) r ht hsmall htotal
    change S / 10 ≤ factorMass w v at hvl
    change factorMass w v < S / 10 + S / 10 at hvu
    have hsum := factorMass_add_sdiff w hvr
    refine ⟨v, hvr, ⟨hvl, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith only [hvu, hS]
    · linarith only [hsum, hr.1, hvu, hS]
    · linarith only [hsum, hr.2, hvl]

/-- A large atom, a large pair, or a simultaneous balanced two- and three-factor partition.
The third group is the complement of the first two, so the groups are disjoint and exhaustive. -/
theorem factorMass_balanced_three_partition {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (s : Finset ι) :
    (∃ i ∈ s, 2 * factorMass w s / 5 ≤ |w i|) ∨
    (∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ 3 * factorMass w s / 5 ≤ |w i| + |w j|) ∨
    ∃ u ⊆ s, ∃ v ⊆ s \ u,
      factorMass w u ∈ Set.Icc (2 * factorMass w s / 5) (factorMass w s / 2) ∧
      factorMass w v ∈ Set.Icc (factorMass w s / 10) (factorMass w s / 2) ∧
      factorMass w ((s \ u) \ v) ∈ Set.Icc (factorMass w s / 10) (factorMass w s / 2) := by
  classical
  by_cases hpos : 0 < factorMass w s
  · by_cases hsingle : ∃ i ∈ s, 2 * factorMass w s / 5 ≤ |w i|
    · exact Or.inl hsingle
    right
    by_cases hpair : ∃ i ∈ s, ∃ j ∈ s,
        i ≠ j ∧ 3 * factorMass w s / 5 ≤ |w i| + |w j|
    · exact Or.inl hpair
    right
    have hcap : ∀ i ∈ s, |w i| < 2 * factorMass w s / 5 := fun i hi =>
      lt_of_not_ge (fun h => hsingle ⟨i, hi, h⟩)
    have hpaircap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        |w i| + |w j| < 3 * factorMass w s / 5 := fun i hi j hj hij =>
      lt_of_not_ge (fun h => hpair ⟨i, hi, j, hj, hij, h⟩)
    obtain ⟨u, hus, hu⟩ :=
      exists_two_fifths_half_subset w s (factorMass w s) hpos rfl hcap hpaircap
    have hsum := factorMass_add_sdiff w hus
    have hr : factorMass w (s \ u) ∈ Set.Icc (factorMass w s / 2) (3 * factorMass w s / 5) :=
      ⟨by linarith only [hsum, hu.2], by linarith only [hsum, hu.1]⟩
    obtain ⟨v, hvr, hv, hz⟩ := split_remainder_into_two w (s \ u) (factorMass w s)
      hpos hr (fun i hi => hcap i (Finset.mem_sdiff.mp hi).1)
    exact ⟨u, hus, v, hvr, hu, hv, hz⟩
  · have hnonneg : 0 ≤ factorMass w s := Finset.sum_nonneg fun i _ => abs_nonneg (w i)
    have hz : factorMass w s = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
    refine Or.inr (Or.inr ⟨s, fun _ h => h, ∅, Finset.empty_subset _, ?_⟩)
    simp only [Finset.sdiff_self, factorMass_empty, hz,
      mul_zero, zero_div, Set.mem_Icc, le_refl, and_self]

#print axioms factorMass_balanced_three_partition

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
