import Mathlib

/-!
# Unique super-increasing source representation

A positive monotone gap sequence with every consecutive step `r`-super-increasing
(`r * bnat n < bnat (n + 1)`) represents each achievable `r`-fold multiset sum uniquely: if a
source multiset `s` and a *distinct-scale* target multiset `t` (both of size `≤ r`) have equal
`bnat`-mass `∑ bnat`, then `s = t` (`multiset_source_unique`).

This is the distinct-index generalisation of the balanced overshoot lemmas
(`all_eq_of_sum_bnat_gt`): there all target scales coincide, here they are spread across distinct
scales.  It is the combinatorial core that isolates a differential-monomial coefficient at a
distinct-index probe as a single permanent over the target scales.
-/

open Finset

namespace GaloisForLFunctions

/-- **Unique super-increasing representation.**  With every consecutive gap `r`-super-increasing
and the gap sequence positive, a size-`≤ r` source multiset and a *distinct-scale* target multiset
of equal `bnat`-mass coincide.  Proof peels the maximal target scale: no source overshoots it, at
least one source attains it (else the whole mass falls a gap short), and at most one does (two
would double the top mass, exceeding the target total), so the top scale matches with multiplicity
one and the rest follows by induction. -/
theorem multiset_source_unique {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ}
    (hb0 : 0 < bnat 0) (hstair : ∀ n, r * bnat n < bnat (n + 1)) :
    ∀ {s t : Multiset ℕ}, s.card ≤ r → s.card = t.card → t.Nodup →
      (s.map bnat).sum = (t.map bnat).sum → s = t := by
  classical
  intro s t
  induction t using Multiset.strongInductionOn generalizing s with
  | _ t IH =>
    intro hsr hcard hnodup hsum
    rcases Multiset.empty_or_exists_mem t with ht0 | ⟨_, _⟩
    · subst ht0
      simp only [Multiset.card_zero] at hcard
      exact Multiset.card_eq_zero.mp (by omega)
    · have htne : t ≠ 0 := by rintro rfl; simp_all
      have htcr : t.card ≤ r := by omega
      obtain ⟨m, hmt, hmax⟩ : ∃ m ∈ t, ∀ x ∈ t, x ≤ m := by
        have hne : t.toFinset.Nonempty := by
          rw [Multiset.toFinset_nonempty]; exact htne
        refine ⟨t.toFinset.max' hne, ?_, ?_⟩
        · rw [← Multiset.mem_toFinset]; exact t.toFinset.max'_mem hne
        · intro x hx; exact t.toFinset.le_max' x (Multiset.mem_toFinset.mpr hx)
      have hpos_m : 0 < bnat m := lt_of_lt_of_le hb0 (hmono (Nat.zero_le m))
      have htsplit : (t.map bnat).sum = bnat m + ((t.erase m).map bnat).sum := by
        conv_lhs => rw [← Multiset.cons_erase hmt]
        rw [Multiset.map_cons, Multiset.sum_cons]
      -- every element of `t` other than `m` is strictly below `m` (distinct scales)
      have hlt_m : ∀ x ∈ t.erase m, x < m := by
        intro x hx
        have hxt : x ∈ t := Multiset.mem_of_mem_erase hx
        rcases lt_or_eq_of_le (hmax x hxt) with h | h
        · exact h
        · exfalso; subst h
          have hcx : t.count x ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnodup x
          have hcx2 : 1 ≤ (t.erase x).count x := Multiset.one_le_count_iff_mem.mpr hx
          have := Multiset.count_erase_self x t
          omega
      -- any scale below `m` is `r`-dominated by `m`
      have key : ∀ x, x < m → r * bnat x < bnat m := fun x hx =>
        lt_of_lt_of_le (hstair x) (hmono hx)
      -- generic upper bound for a mass supported on scales `< m`
      have massbound : ∀ (u : Multiset ℕ), u.card ≤ r → (∀ x ∈ u, x < m) →
          (u.map bnat).sum < bnat m := by
        intro u hucard hult
        rcases Multiset.empty_or_exists_mem u with he | ⟨y, hy⟩
        · rw [he]; simpa using hpos_m
        · obtain ⟨ymax, hymaxmem, hymaxmax⟩ : ∃ z ∈ u, ∀ w ∈ u, bnat w ≤ bnat z := by
            have hne : u.toFinset.Nonempty :=
              Multiset.toFinset_nonempty.mpr (by rintro h0; rw [h0] at hy; simp at hy)
            refine ⟨u.toFinset.max' hne, ?_, ?_⟩
            · rw [← Multiset.mem_toFinset]; exact u.toFinset.max'_mem hne
            · intro w hw; exact hmono (u.toFinset.le_max' w (Multiset.mem_toFinset.mpr hw))
          have hsum_le : (u.map bnat).sum ≤ u.card * bnat ymax := by
            have := Multiset.sum_le_card_nsmul (u.map bnat) (bnat ymax) (by
              intro z hz; obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz; exact hymaxmax w hw)
            rwa [Multiset.card_map, smul_eq_mul] at this
          calc (u.map bnat).sum ≤ u.card * bnat ymax := hsum_le
            _ ≤ r * bnat ymax := Nat.mul_le_mul_right _ hucard
            _ < bnat m := key ymax (hult ymax hymaxmem)
      have hbelow : ((t.erase m).map bnat).sum < bnat m :=
        massbound (t.erase m) (le_trans (Multiset.card_le_card (Multiset.erase_le m t)) htcr) hlt_m
      have htgt_lb : bnat m ≤ (t.map bnat).sum := by rw [htsplit]; omega
      have htgt_ub : (t.map bnat).sum < 2 * bnat m := by rw [htsplit]; omega
      -- no source overshoots `m`
      have hsource_le : ∀ x ∈ s, x ≤ m := by
        intro x hx
        by_contra hlt
        rw [not_le] at hlt
        have hbig : bnat (m + 1) ≤ bnat x := hmono hlt
        have hxle : bnat x ≤ (s.map bnat).sum :=
          Multiset.single_le_sum (fun z _ => Nat.zero_le z) (bnat x) (Multiset.mem_map_of_mem bnat hx)
        have htarget_le : (t.map bnat).sum ≤ r * bnat m := by
          have := Multiset.sum_le_card_nsmul (t.map bnat) (bnat m) (by
            intro z hz; obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz; exact hmono (hmax w hw))
          rw [Multiset.card_map, smul_eq_mul] at this
          exact le_trans this (Nat.mul_le_mul_right _ htcr)
        have := hstair m
        omega
      -- `m` occurs in `s`
      have hcount_pos : 1 ≤ s.count m := by
        by_contra h
        rw [not_le] at h
        have hnotmem : m ∉ s := Multiset.count_eq_zero.mp (by omega)
        have hsrc_lt : ∀ x ∈ s, x < m := by
          intro x hx
          rcases lt_or_eq_of_le (hsource_le x hx) with h' | h'
          · exact h'
          · exact absurd (h' ▸ hx) hnotmem
        have hsmall := massbound s hsr hsrc_lt
        rw [hsum] at hsmall; omega
      -- `m` occurs at most once in `s`
      have hcount_le : s.count m ≤ 1 := by
        by_contra h
        rw [not_le] at h
        have hrep : Multiset.replicate 2 m ≤ s :=
          Multiset.le_iff_count.mpr (by
            intro a; rcases eq_or_ne a m with rfl | hne
            · simp only [Multiset.count_replicate_self]; omega
            · simp only [Multiset.count_replicate, if_neg (Ne.symm hne)]; exact Nat.zero_le _)
        have hmaple : (Multiset.replicate 2 m).map bnat ≤ s.map bnat := Multiset.map_le_map hrep
        obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hmaple
        have h2le : ((Multiset.replicate 2 m).map bnat).sum ≤ (s.map bnat).sum := by
          rw [hu, Multiset.sum_add]; exact Nat.le_add_right _ _
        have h2eq : ((Multiset.replicate 2 m).map bnat).sum = 2 * bnat m := by
          rw [Multiset.map_replicate, Multiset.sum_replicate]; ring
        rw [h2eq, hsum] at h2le; omega
      have hcount_eq : s.count m = 1 := le_antisymm hcount_le hcount_pos
      have hms : m ∈ s := Multiset.count_pos.mp (by omega)
      have hcard' : (s.erase m).card = (t.erase m).card := by
        rw [Multiset.card_erase_of_mem hms, Multiset.card_erase_of_mem hmt, hcard]
      have hcardsr : (s.erase m).card ≤ r :=
        le_trans (Multiset.card_le_card (Multiset.erase_le m s)) hsr
      have hnodup' : (t.erase m).Nodup := hnodup.erase m
      have hsum' : ((s.erase m).map bnat).sum = ((t.erase m).map bnat).sum := by
        have hs2 : (s.map bnat).sum = bnat m + ((s.erase m).map bnat).sum := by
          conv_lhs => rw [← Multiset.cons_erase hms]
          rw [Multiset.map_cons, Multiset.sum_cons]
        rw [hs2, htsplit] at hsum; omega
      have hlt' : t.erase m < t := Multiset.erase_lt.mpr hmt
      have hrec := IH (t.erase m) hlt' hcardsr hcard' hnodup' hsum'
      rw [← Multiset.cons_erase hms, ← Multiset.cons_erase hmt, hrec]

/-- **Window uniqueness.**  Strengthening of `multiset_source_unique` allowing the source `bnat`-mass
to lie within a window `W` of the target mass (`r·bnat n + W < bnat (n+1)`): the source multiset still
coincides with the distinct-scale target, and the masses are in fact exactly equal.  This is the
distinct-index degree/order separation: a differential monomial of the wrong total order probes a
mass off the target by a bounded amount, which the window forbids. -/
theorem multiset_source_window_unique {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1)) :
    ∀ {s t : Multiset ℕ}, s.card ≤ r → s.card = t.card → t.Nodup →
      (s.map bnat).sum ≤ (t.map bnat).sum + W → (t.map bnat).sum ≤ (s.map bnat).sum + W →
      s = t ∧ (s.map bnat).sum = (t.map bnat).sum := by
  classical
  intro s t
  induction t using Multiset.strongInductionOn generalizing s with
  | _ t IH =>
    intro hsr hcard hnodup hle1 hle2
    rcases Multiset.empty_or_exists_mem t with ht0 | ⟨_, _⟩
    · subst ht0
      simp only [Multiset.card_zero] at hcard
      have hs0 : s = 0 := Multiset.card_eq_zero.mp (by omega)
      exact ⟨hs0, by rw [hs0]⟩
    · have htne : t ≠ 0 := by rintro rfl; simp_all
      have htcr : t.card ≤ r := by omega
      have hr1 : 1 ≤ r := by
        have : 1 ≤ t.card := Multiset.card_pos.mpr htne
        omega
      obtain ⟨m, hmt, hmax⟩ : ∃ m ∈ t, ∀ x ∈ t, x ≤ m := by
        have hne : t.toFinset.Nonempty := by rw [Multiset.toFinset_nonempty]; exact htne
        refine ⟨t.toFinset.max' hne, ?_, ?_⟩
        · rw [← Multiset.mem_toFinset]; exact t.toFinset.max'_mem hne
        · intro x hx; exact t.toFinset.le_max' x (Multiset.mem_toFinset.mpr hx)
      have hpos_m : 0 < bnat m := lt_of_lt_of_le hb0 (hmono (Nat.zero_le m))
      have htsplit : (t.map bnat).sum = bnat m + ((t.erase m).map bnat).sum := by
        conv_lhs => rw [← Multiset.cons_erase hmt]
        rw [Multiset.map_cons, Multiset.sum_cons]
      have hlt_m : ∀ x ∈ t.erase m, x < m := by
        intro x hx
        have hxt : x ∈ t := Multiset.mem_of_mem_erase hx
        rcases lt_or_eq_of_le (hmax x hxt) with h | h
        · exact h
        · exfalso; subst h
          have hcx : t.count x ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnodup x
          have hcx2 : 1 ≤ (t.erase x).count x := Multiset.one_le_count_iff_mem.mpr hx
          have := Multiset.count_erase_self x t
          omega
      -- any scale below `m` is `r`-with-window dominated by `m`
      have key : ∀ x, x < m → r * bnat x + W < bnat m := fun x hx =>
        lt_of_lt_of_le (hW x) (hmono hx)
      have massbound : ∀ (u : Multiset ℕ), u.card ≤ r → (∀ x ∈ u, x < m) →
          (u.map bnat).sum + W < bnat m := by
        intro u hucard hult
        rcases Multiset.empty_or_exists_mem u with he | ⟨y, hy⟩
        · rw [he]; simpa using lt_of_lt_of_le hWb (hmono (Nat.zero_le m))
        · obtain ⟨ymax, hymaxmem, hymaxmax⟩ : ∃ z ∈ u, ∀ w ∈ u, bnat w ≤ bnat z := by
            have hne : u.toFinset.Nonempty :=
              Multiset.toFinset_nonempty.mpr (by rintro h0; rw [h0] at hy; simp at hy)
            refine ⟨u.toFinset.max' hne, ?_, ?_⟩
            · rw [← Multiset.mem_toFinset]; exact u.toFinset.max'_mem hne
            · intro w hw; exact hmono (u.toFinset.le_max' w (Multiset.mem_toFinset.mpr hw))
          have hsum_le : (u.map bnat).sum ≤ u.card * bnat ymax := by
            have := Multiset.sum_le_card_nsmul (u.map bnat) (bnat ymax) (by
              intro z hz; obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz; exact hymaxmax w hw)
            rwa [Multiset.card_map, smul_eq_mul] at this
          calc (u.map bnat).sum + W ≤ u.card * bnat ymax + W := by omega
            _ ≤ r * bnat ymax + W := by have := Nat.mul_le_mul_right (bnat ymax) hucard; omega
            _ < bnat m := key ymax (hult ymax hymaxmem)
      have hbelow : ((t.erase m).map bnat).sum + W < bnat m :=
        massbound (t.erase m) (le_trans (Multiset.card_le_card (Multiset.erase_le m t)) htcr) hlt_m
      -- no source overshoots `m`
      have hsource_le : ∀ x ∈ s, x ≤ m := by
        intro x hx
        by_contra hlt
        rw [not_le] at hlt
        have hbig : bnat (m + 1) ≤ bnat x := hmono hlt
        have hxle : bnat x ≤ (s.map bnat).sum :=
          Multiset.single_le_sum (fun z _ => Nat.zero_le z) (bnat x) (Multiset.mem_map_of_mem bnat hx)
        have htarget_le : (t.map bnat).sum ≤ r * bnat m := by
          have := Multiset.sum_le_card_nsmul (t.map bnat) (bnat m) (by
            intro z hz; obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz; exact hmono (hmax w hw))
          rw [Multiset.card_map, smul_eq_mul] at this
          exact le_trans this (Nat.mul_le_mul_right _ htcr)
        have := hW m
        omega
      -- `m` occurs in `s`
      have hcount_pos : 1 ≤ s.count m := by
        by_contra h
        rw [not_le] at h
        have hnotmem : m ∉ s := Multiset.count_eq_zero.mp (by omega)
        have hsrc_lt : ∀ x ∈ s, x < m := by
          intro x hx
          rcases lt_or_eq_of_le (hsource_le x hx) with h' | h'
          · exact h'
          · exact absurd (h' ▸ hx) hnotmem
        have hsmall := massbound s hsr hsrc_lt
        -- t-mass ≥ bnat m, s-mass + W < bnat m
        have : bnat m ≤ (t.map bnat).sum := by rw [htsplit]; omega
        omega
      -- `m` occurs at most once in `s`
      have hcount_le : s.count m ≤ 1 := by
        by_contra h
        rw [not_le] at h
        have hrep : Multiset.replicate 2 m ≤ s :=
          Multiset.le_iff_count.mpr (by
            intro a; rcases eq_or_ne a m with rfl | hne
            · simp only [Multiset.count_replicate_self]; omega
            · simp only [Multiset.count_replicate, if_neg (Ne.symm hne)]; exact Nat.zero_le _)
        have hmaple : (Multiset.replicate 2 m).map bnat ≤ s.map bnat := Multiset.map_le_map hrep
        obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hmaple
        have h2le : ((Multiset.replicate 2 m).map bnat).sum ≤ (s.map bnat).sum := by
          rw [hu, Multiset.sum_add]; exact Nat.le_add_right _ _
        have h2eq : ((Multiset.replicate 2 m).map bnat).sum = 2 * bnat m := by
          rw [Multiset.map_replicate, Multiset.sum_replicate]; ring
        -- s-mass ≥ 2 bnat m, t-mass = bnat m + (erase), s ≤ t + W
        rw [h2eq] at h2le
        have htub : (t.map bnat).sum + W < 2 * bnat m := by rw [htsplit]; omega
        omega
      have hcount_eq : s.count m = 1 := le_antisymm hcount_le hcount_pos
      have hms : m ∈ s := Multiset.count_pos.mp (by omega)
      have hcard' : (s.erase m).card = (t.erase m).card := by
        rw [Multiset.card_erase_of_mem hms, Multiset.card_erase_of_mem hmt, hcard]
      have hcardsr : (s.erase m).card ≤ r :=
        le_trans (Multiset.card_le_card (Multiset.erase_le m s)) hsr
      have hnodup' : (t.erase m).Nodup := hnodup.erase m
      have hssplit : (s.map bnat).sum = bnat m + ((s.erase m).map bnat).sum := by
        conv_lhs => rw [← Multiset.cons_erase hms]
        rw [Multiset.map_cons, Multiset.sum_cons]
      have hle1' : ((s.erase m).map bnat).sum ≤ ((t.erase m).map bnat).sum + W := by
        rw [hssplit, htsplit] at hle1; omega
      have hle2' : ((t.erase m).map bnat).sum ≤ ((s.erase m).map bnat).sum + W := by
        rw [hssplit, htsplit] at hle2; omega
      have hlt' : t.erase m < t := Multiset.erase_lt.mpr hmt
      obtain ⟨hrec, hmasseq⟩ := IH (t.erase m) hlt' hcardsr hcard' hnodup' hle1' hle2'
      refine ⟨by rw [← Multiset.cons_erase hms, ← Multiset.cons_erase hmt, hrec], ?_⟩
      rw [hssplit, htsplit, hmasseq]

end GaloisForLFunctions
