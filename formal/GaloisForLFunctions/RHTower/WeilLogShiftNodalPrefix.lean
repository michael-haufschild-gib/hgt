import GaloisForLFunctions.RHTower.WeilLogShiftNodalDeletion

/-! Strict signs of separated nodal prefix sums, including their endpoint boundary. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilNodalPrefix_sign {ι : Type*} [DecidableEq ι]
    (s p : Finset ι) (h : ι → ℝ) (hinj : Set.InjOn h ↑s)
    (hps : p ⊆ s) (hp : p.Nonempty)
    (hsep : ∀ i ∈ p, ∀ j ∈ s, j ∉ p → h i < h j) :
    0 ≤ (-1 : ℝ) ^ (s.card - p.card) * ∑ i ∈ p, Lagrange.nodalWeight s h i ∧
      (p ≠ s ∨ s.card = 1 →
        0 < (-1 : ℝ) ^ (s.card - p.card) * ∑ i ∈ p, Lagrange.nodalWeight s h i) := by
  induction s using Finset.strongInduction generalizing p with
  | H s ih =>
    by_cases hfull : p = s
    · subst p
      by_cases hone : s.card = 1
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hone
        norm_num [Lagrange.nodalWeight]
      · have hcard : 2 ≤ s.card := by
          have := Finset.card_pos.mpr hp
          omega
        rw [finiteWeilNodalWeight_sum_eq_zero s h hinj hcard, mul_zero]
        simp [hone]
    · obtain ⟨a, ha⟩ := hp
      have hsp : ¬s ⊆ p := fun e => hfull (Finset.Subset.antisymm hps e)
      obtain ⟨b, hb⟩ := Finset.sdiff_nonempty.mpr hsp
      obtain ⟨hbs, hbp⟩ := Finset.mem_sdiff.mp hb
      have hab : a ≠ b := fun e => hbp (e ▸ ha)
      have hpsL : p ⊆ s.erase b := Finset.subset_erase.mpr ⟨hps, hbp⟩
      have hpsR : p.erase a ⊆ s.erase a := Finset.erase_subset_erase a hps
      have hL := ih (s.erase b) (Finset.erase_ssubset hbs) p
        (hinj.mono (Finset.erase_subset b s)) hpsL ⟨a, ha⟩
        (fun i hi j hj hnot => hsep i hi j (Finset.mem_of_mem_erase hj) hnot)
      have hcount : p.card < s.card := by
        have hc := Finset.card_le_card hps
        by_contra he
        exact hfull (Finset.eq_of_subset_of_card_le hps (by omega))
      have hphase : (-1 : ℝ) ^ (s.card - p.card) =
          -(-1 : ℝ) ^ ((s.erase b).card - p.card) := by
        have hc : s.card - p.card = (s.erase b).card - p.card + 1 := by
          rw [Finset.card_erase_of_mem hbs]
          omega
        rw [hc, pow_succ]
        ring
      have hrightcard : (s.erase a).card - (p.erase a).card = s.card - p.card := by
        rw [Finset.card_erase_of_mem (hps ha), Finset.card_erase_of_mem ha]
        have hc := Finset.card_pos.mpr (show p.Nonempty from ⟨a, ha⟩)
        omega
      have hR : 0 ≤ (-1 : ℝ) ^ (s.card - p.card) *
          ∑ i ∈ p.erase a, Lagrange.nodalWeight (s.erase a) h i ∧
          ((p.erase a).Nonempty → 0 < (-1 : ℝ) ^ (s.card - p.card) *
            ∑ i ∈ p.erase a, Lagrange.nodalWeight (s.erase a) h i) := by
        by_cases hpR : (p.erase a).Nonempty
        · have hsepR : ∀ i ∈ p.erase a, ∀ j ∈ s.erase a,
              j ∉ p.erase a → h i < h j := by
            intro i hi j hj hnot
            apply hsep i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj)
            exact fun e => hnot (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, e⟩)
          have ht := ih (s.erase a) (Finset.erase_ssubset (hps ha)) (p.erase a)
            (hinj.mono (Finset.erase_subset a s)) hpsR hpR hsepR
          rw [hrightcard] at ht
          have hne : p.erase a ≠ s.erase a := by
            intro e
            have hbR : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab.symm, hbs⟩
            rw [← e] at hbR
            exact hbp (Finset.mem_of_mem_erase hbR)
          exact ⟨ht.1, fun _ => ht.2 (Or.inl hne)⟩
        · have he : p.erase a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpR
          simp [he]
      have hsumpos : 0 <
          (-1 : ℝ) ^ ((s.erase b).card - p.card) *
            (∑ i ∈ p, Lagrange.nodalWeight (s.erase b) h i) +
          (-1 : ℝ) ^ (s.card - p.card) *
            (∑ i ∈ p.erase a, Lagrange.nodalWeight (s.erase a) h i) := by
        by_cases hpR : (p.erase a).Nonempty
        · exact add_pos_of_nonneg_of_pos hL.1 (hR.2 hpR)
        · have he : p.erase a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpR
          have hpone : p.card = 1 := by
            have hc := Finset.card_erase_of_mem ha
            rw [he, Finset.card_empty] at hc
            have hpos := Finset.card_pos.mpr (show p.Nonempty from ⟨a, ha⟩)
            omega
          have hstrict : p ≠ s.erase b ∨ (s.erase b).card = 1 := by
            by_cases heq : p = s.erase b
            · exact Or.inr (heq ▸ hpone)
            · exact Or.inl heq
          exact add_pos_of_pos_of_nonneg (hL.2 hstrict) hR.1
      have hrec := finiteWeilNodalPrefix_deletion s p h hinj hps ha hbs hbp
      have hid : (h b - h a) * ((-1 : ℝ) ^ (s.card - p.card) *
          ∑ i ∈ p, Lagrange.nodalWeight s h i) =
          (-1 : ℝ) ^ ((s.erase b).card - p.card) *
            (∑ i ∈ p, Lagrange.nodalWeight (s.erase b) h i) +
          (-1 : ℝ) ^ (s.card - p.card) *
            (∑ i ∈ p.erase a, Lagrange.nodalWeight (s.erase a) h i) := by
        rw [hphase]
        linear_combination -((-1 : ℝ) ^ ((s.erase b).card - p.card)) * hrec
      have hgap : 0 < h b - h a := sub_pos.mpr (hsep a ha b hbs hbp)
      have hpos : 0 < (-1 : ℝ) ^ (s.card - p.card) *
          ∑ i ∈ p, Lagrange.nodalWeight s h i := by
        rw [← hid] at hsumpos
        nlinarith
      exact ⟨le_of_lt hpos, fun _ => hpos⟩

theorem finiteWeilNodalPrefix_pos {ι : Type*} [DecidableEq ι]
    (s p : Finset ι) (h : ι → ℝ) (hinj : Set.InjOn h ↑s)
    (hps : p ⊆ s) (hp : p.Nonempty) (hproper : p ≠ s)
    (hsep : ∀ i ∈ p, ∀ j ∈ s, j ∉ p → h i < h j) :
    0 < (-1 : ℝ) ^ (s.card - p.card) * ∑ i ∈ p, Lagrange.nodalWeight s h i :=
  (finiteWeilNodalPrefix_sign s p h hinj hps hp hsep).2 (Or.inl hproper)

end RHTower
