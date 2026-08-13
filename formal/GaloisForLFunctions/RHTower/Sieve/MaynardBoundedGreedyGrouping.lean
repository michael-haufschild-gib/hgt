import GaloisForLFunctions.RHTower.Sieve.MaynardGreedyGroupSelection

/-!
# Greedy grouping below an arbitrary height exponent

The old robust partition assumes every atom has mass at most `2t`.  For global Route-T counting
we instead remove atoms at or above the height and group every remaining atom, whose mass is only
known to be below `1`.  The same minimal-heavy construction gives groups in `[t,B+2t)` whenever
all atoms have mass at most `B`.
-/

noncomputable section
namespace RHTower.Sieve

open Finset

/-- Threshold packing with arbitrary atom cap `B`. -/
def IsBoundedWeightPacking {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t B : ℝ) (s : Finset ι)
    (groups : List (Finset ι)) : Prop :=
  groups.Pairwise Disjoint ∧
    (∀ u ∈ groups, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < B + 2 * t) ∧
    groups.foldr (· ∪ ·) ∅ = s

/-- A minimal threshold-heavy subset has mass below `t+B`. -/
theorem exists_minimal_bounded_weight_group
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t B : ℝ) (s : Finset ι)
    (ht : 0 < t) (hwB : ∀ i ∈ s, w i ≤ B)
    (htotal : t ≤ ∑ i ∈ s, w i) :
    ∃ u : Finset ι, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < t + B := by
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
  have hiupper := hwB i hiS
  have hsum := Finset.sum_erase_add u w hi
  exact ⟨u, ⟨i, hi⟩, huinfo.1, huinfo.2, by linarith⟩

/-- Every capped finite family of total mass at least `t` has a genuine partition into groups of
mass in `[t,B+2t)`. -/
theorem exists_bounded_weight_packing
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t B : ℝ) (s : Finset ι)
    (ht : 0 < t) (hwB : ∀ i ∈ s, w i ≤ B)
    (htotal : t ≤ ∑ i ∈ s, w i) :
    ∃ groups : List (Finset ι), IsBoundedWeightPacking w t B s groups := by
  classical
  revert hwB htotal
  refine Finset.strongInduction (p := fun s =>
    (∀ i ∈ s, w i ≤ B) → t ≤ ∑ i ∈ s, w i →
      ∃ groups : List (Finset ι), IsBoundedWeightPacking w t B s groups) ?_ s
  intro s ih hwB htotal
  obtain ⟨u, hune, hus, hulower, huupper⟩ :=
    exists_minimal_bounded_weight_group w t B s ht hwB htotal
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
    obtain ⟨groups, hpair, hgroups, hcover⟩ :=
      ih r hrproper hrwB hrtotal
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
    have hsupper : (∑ i ∈ s, w i) < B + 2 * t := by
      dsimp [r] at hrupper
      linarith
    have hsne : s.Nonempty := hune.mono hus
    refine ⟨[s], ?_⟩
    simp [IsBoundedWeightPacking, hsne, htotal, hsupper]

/-- A bounded packing of positive total mass is nonempty. -/
theorem boundedWeightPacking_ne_nil
    {ι : Type*} [DecidableEq ι] {w : ι → ℝ} {t B : ℝ} {s : Finset ι}
    {groups : List (Finset ι)} (ht : 0 < t)
    (htotal : t ≤ ∑ i ∈ s, w i)
    (hpacking : IsBoundedWeightPacking w t B s groups) : groups ≠ [] := by
  intro hnil
  subst groups
  have hs : s = ∅ := by
    simpa [IsBoundedWeightPacking] using hpacking.2.2.symm
  subst s
  simp at htotal
  linarith

/-- A bounded packing inherits the same multiplicative large-group pigeonhole as the robust
all-short packing. -/
theorem exists_large_group_mem_bounded_packing
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t B : ℝ) (s : Finset ι)
    (groups : List (Finset ι))
    (ht : 0 < t) (htotal : t ≤ ∑ i ∈ s, w i)
    (hpacking : IsBoundedWeightPacking w t B s groups)
    (A : ι → ℝ) (z : ι → ℂ) (e : ℝ)
    (hA : ∀ i ∈ s, 0 < A i)
    (hlarge : (∏ i ∈ s, A i) ^ e ≤ ‖∏ i ∈ s, z i‖) :
    ∃ u ∈ groups, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < B + 2 * t ∧
      (∏ i ∈ u, A i) ^ e ≤ ‖∏ i ∈ u, z i‖ := by
  classical
  have hne := boundedWeightPacking_ne_nil ht htotal hpacking
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
      (show (∏ j, groupA j) ^ e ≤ ∏ j, groupV j by
        rw [hprodA, hprodZ]
        exact hlarge)
  obtain ⟨j, hj⟩ := hselected
  let u := groups.get j
  have hu : u ∈ groups := List.get_mem groups j
  obtain ⟨hune, hus, hulower, huupper⟩ := hpacking.2.1 u hu
  exact ⟨u, hu, hune, hus, hulower, huupper, hj⟩

/-- Constructed bounded-group large-value selector. -/
theorem exists_bounded_greedy_large_group
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t B : ℝ) (s : Finset ι)
    (ht : 0 < t) (hwB : ∀ i ∈ s, w i ≤ B)
    (htotal : t ≤ ∑ i ∈ s, w i)
    (A : ι → ℝ) (z : ι → ℂ) (e : ℝ)
    (hA : ∀ i ∈ s, 0 < A i)
    (hlarge : (∏ i ∈ s, A i) ^ e ≤ ‖∏ i ∈ s, z i‖) :
    ∃ u : Finset ι, u.Nonempty ∧ u ⊆ s ∧
      t ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i < B + 2 * t ∧
      (∏ i ∈ u, A i) ^ e ≤ ‖∏ i ∈ u, z i‖ := by
  obtain ⟨groups, hpacking⟩ :=
    exists_bounded_weight_packing w t B s ht hwB htotal
  obtain ⟨u, _hu, hune, hus, hulower, huupper, hgroup⟩ :=
    exists_large_group_mem_bounded_packing
      w t B s groups ht htotal hpacking A z e hA hlarge
  exact ⟨u, hune, hus, hulower, huupper, hgroup⟩

/-- Removing factors already known to lie below their individual amplitude threshold preserves
the product threshold on the remaining family. -/
theorem restricted_product_large_of_complement_small
    {ι : Type*} [DecidableEq ι]
    (s good : Finset ι) (hgood : good ⊆ s)
    (A v : ι → ℝ) (e : ℝ)
    (hA : ∀ i ∈ s, 0 < A i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (hbad : ∀ i ∈ s \ good, v i ≤ A i ^ e)
    (hlarge : (∏ i ∈ s, A i) ^ e ≤ ∏ i ∈ s, v i) :
    (∏ i ∈ good, A i) ^ e ≤ ∏ i ∈ good, v i := by
  let bad : Finset ι := s \ good
  have hbadSub : bad ⊆ s := Finset.sdiff_subset
  have hAg : 0 < ∏ i ∈ good, A i :=
    Finset.prod_pos fun i hi => hA i (hgood hi)
  have hAb : 0 < ∏ i ∈ bad, A i :=
    Finset.prod_pos fun i hi => hA i (hbadSub hi)
  have hvg : 0 ≤ ∏ i ∈ good, v i :=
    Finset.prod_nonneg fun i hi => hv i (hgood hi)
  have hvb : 0 ≤ ∏ i ∈ bad, v i :=
    Finset.prod_nonneg fun i hi => hv i (hbadSub hi)
  have hvbad : ∏ i ∈ bad, v i ≤ ∏ i ∈ bad, A i ^ e :=
    Finset.prod_le_prod (fun i hi => hv i (hbadSub hi)) fun i hi => hbad i hi
  have hAbPow : ∏ i ∈ bad, A i ^ e = (∏ i ∈ bad, A i) ^ e :=
    Real.finsetProd_rpow bad A (fun i hi => (hA i (hbadSub hi)).le) e
  have hsplitA : ∏ i ∈ s, A i = (∏ i ∈ good, A i) * ∏ i ∈ bad, A i := by
    dsimp only [bad]
    calc
      ∏ i ∈ s, A i = (∏ i ∈ s \ good, A i) * ∏ i ∈ good, A i :=
        (Finset.prod_sdiff hgood).symm
      _ = (∏ i ∈ good, A i) * ∏ i ∈ s \ good, A i := by ring
  have hsplitV : ∏ i ∈ s, v i = (∏ i ∈ good, v i) * ∏ i ∈ bad, v i := by
    dsimp only [bad]
    calc
      ∏ i ∈ s, v i = (∏ i ∈ s \ good, v i) * ∏ i ∈ good, v i :=
        (Finset.prod_sdiff hgood).symm
      _ = (∏ i ∈ good, v i) * ∏ i ∈ s \ good, v i := by ring
  have hsplitPow :
      ((∏ i ∈ good, A i) * ∏ i ∈ bad, A i) ^ e =
        (∏ i ∈ good, A i) ^ e * (∏ i ∈ bad, A i) ^ e := by
    exact Real.mul_rpow hAg.le hAb.le
  have hcombined :
      (∏ i ∈ good, A i) ^ e * (∏ i ∈ bad, A i) ^ e ≤
        (∏ i ∈ good, v i) * (∏ i ∈ bad, v i) := by
    rw [← hsplitPow, ← hsplitA, ← hsplitV]
    exact hlarge
  have hbadPow : ∏ i ∈ bad, v i ≤ (∏ i ∈ bad, A i) ^ e := by
    rw [← hAbPow]
    exact hvbad
  have hupper :
      (∏ i ∈ good, v i) * (∏ i ∈ bad, v i) ≤
        (∏ i ∈ good, v i) * (∏ i ∈ bad, A i) ^ e :=
    mul_le_mul_of_nonneg_left hbadPow hvg
  have hcancel := hcombined.trans hupper
  have hAbPowPos : 0 < (∏ i ∈ bad, A i) ^ e :=
    Real.rpow_pos_of_pos hAb _
  exact (mul_le_mul_iff_right₀ hAbPowPos).mp (by
    simpa [mul_comm] using hcancel)

/-- Complex-norm form of complement removal. -/
theorem restricted_complex_product_large_of_complement_small
    {ι : Type*} [DecidableEq ι]
    (s good : Finset ι) (hgood : good ⊆ s)
    (A : ι → ℝ) (z : ι → ℂ) (e : ℝ)
    (hA : ∀ i ∈ s, 0 < A i)
    (hbad : ∀ i ∈ s \ good, ‖z i‖ ≤ A i ^ e)
    (hlarge : (∏ i ∈ s, A i) ^ e ≤ ‖∏ i ∈ s, z i‖) :
    (∏ i ∈ good, A i) ^ e ≤ ‖∏ i ∈ good, z i‖ := by
  have h := restricted_product_large_of_complement_small
    s good hgood A (fun i => ‖z i‖) e hA
      (fun i _ => norm_nonneg _) hbad
  rw [Complex.norm_prod]
  exact h (by simpa only [Complex.norm_prod] using hlarge)

end RHTower.Sieve
