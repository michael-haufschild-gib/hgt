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

/-- **Card-free window uniqueness.**  Dropping the equal-cardinality hypothesis: a source multiset
(size `≤ r`) whose `bnat`-mass lies within `W` of a distinct-scale target multiset (also size `≤ r`)
must coincide with it — so their cardinalities are equal.  This is the distinct-index **degree**
separation: a differential monomial of the wrong total degree has a source count differing from the
target, so no source configuration can match. -/
theorem multiset_source_window_free {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1)) :
    ∀ {s t : Multiset ℕ}, s.card ≤ r → t.card ≤ r → t.Nodup →
      (s.map bnat).sum ≤ (t.map bnat).sum + W → (t.map bnat).sum ≤ (s.map bnat).sum + W →
      s = t := by
  classical
  intro s t
  induction t using Multiset.strongInductionOn generalizing s with
  | _ t IH =>
    intro hsr htr hnodup hle1 hle2
    rcases Multiset.empty_or_exists_mem t with ht0 | ⟨_, _⟩
    · subst ht0
      rcases Multiset.empty_or_exists_mem s with hs0 | ⟨y, hy⟩
      · exact hs0
      · exfalso
        have hyle : bnat y ≤ (s.map bnat).sum :=
          Multiset.single_le_sum (fun z _ => Nat.zero_le z) (bnat y) (Multiset.mem_map_of_mem bnat hy)
        have h0y : bnat 0 ≤ bnat y := hmono (Nat.zero_le y)
        simp only [Multiset.map_zero, Multiset.sum_zero, Nat.zero_add] at hle1
        omega
    · have htne : t ≠ 0 := by rintro rfl; simp_all
      have htcr : t.card ≤ r := htr
      have hr1 : 1 ≤ r := le_trans (Multiset.card_pos.mpr htne) htr
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
        have : bnat m ≤ (t.map bnat).sum := by rw [htsplit]; omega
        omega
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
        rw [h2eq] at h2le
        have htub : (t.map bnat).sum + W < 2 * bnat m := by rw [htsplit]; omega
        omega
      have hcount_eq : s.count m = 1 := le_antisymm hcount_le hcount_pos
      have hms : m ∈ s := Multiset.count_pos.mp (by omega)
      have hcardsr : (s.erase m).card ≤ r :=
        le_trans (Multiset.card_le_card (Multiset.erase_le m s)) hsr
      have hcardtr : (t.erase m).card ≤ r :=
        le_trans (Multiset.card_le_card (Multiset.erase_le m t)) htr
      have hnodup' : (t.erase m).Nodup := hnodup.erase m
      have hssplit : (s.map bnat).sum = bnat m + ((s.erase m).map bnat).sum := by
        conv_lhs => rw [← Multiset.cons_erase hms]
        rw [Multiset.map_cons, Multiset.sum_cons]
      have hle1' : ((s.erase m).map bnat).sum ≤ ((t.erase m).map bnat).sum + W := by
        rw [hssplit, htsplit] at hle1; omega
      have hle2' : ((t.erase m).map bnat).sum ≤ ((s.erase m).map bnat).sum + W := by
        rw [hssplit, htsplit] at hle2; omega
      have hlt' : t.erase m < t := Multiset.erase_lt.mpr hmt
      have hrec := IH (t.erase m) hlt' hcardsr hcardtr hnodup' hle1' hle2'
      rw [← Multiset.cons_erase hms, ← Multiset.cons_erase hmt, hrec]

/-- **Unique super-increasing representation.**  With every consecutive gap `r`-super-increasing
and the gap sequence positive, a size-`≤ r` source multiset and a *distinct-scale* target multiset
of equal `bnat`-mass coincide.  This is the empty-window case of
`multiset_source_window_free`: equal cardinalities bound the target size, and exact mass equality
is a window of width zero. -/
theorem multiset_source_unique {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ}
    (hb0 : 0 < bnat 0) (hstair : ∀ n, r * bnat n < bnat (n + 1)) :
    ∀ {s t : Multiset ℕ}, s.card ≤ r → s.card = t.card → t.Nodup →
      (s.map bnat).sum = (t.map bnat).sum → s = t := by
  intro s t hsr hcard hnodup hsum
  exact multiset_source_window_free (W := 0) hmono hb0 hb0
    (fun n => by simpa using hstair n) hsr (hcard ▸ hsr) hnodup
    (by simp [hsum]) (by simp [hsum])

/-- **Window uniqueness.**  Allowing the source `bnat`-mass to lie within a window `W` of the
target mass (`r·bnat n + W < bnat (n+1)`), the source multiset still coincides with the
distinct-scale target, and the masses are in fact exactly equal.  This is the distinct-index
degree/order separation: a differential monomial of the wrong total order probes a mass off the
target by a bounded amount, which the window forbids.  Equal cardinalities bound the target size,
so this is `multiset_source_window_free` with the mass equality read off the resulting identity. -/
theorem multiset_source_window_unique {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1)) :
    ∀ {s t : Multiset ℕ}, s.card ≤ r → s.card = t.card → t.Nodup →
      (s.map bnat).sum ≤ (t.map bnat).sum + W → (t.map bnat).sum ≤ (s.map bnat).sum + W →
      s = t ∧ (s.map bnat).sum = (t.map bnat).sum := by
  intro s t hsr hcard hnodup hle1 hle2
  have hst : s = t :=
    multiset_source_window_free hmono hb0 hWb hW hsr (hcard ▸ hsr) hnodup hle1 hle2
  exact ⟨hst, by rw [hst]⟩

end GaloisForLFunctions
