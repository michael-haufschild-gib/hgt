import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Finset.Card

/-!
# When the sub-multisets of a fixed size are all distinct

The sub-multisets of size `m` of a multiset, enumerated with multiplicity, are pairwise distinct
exactly when the multiset itself has no repeated element — provided `m` is neither `0` nor the whole
size, where the enumeration is a single item either way.

Mathlib proves one direction, that a multiset without repeats has a repeat-free enumeration.  The
converse is what a *characterisation* of a count needs: a repeated element `a` produces a
sub-multiset containing one copy of `a`, and the two copies of `a` supply it twice.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- A multiset has a sub-multiset of every size up to its own. -/
theorem exists_le_card_eq {t : Multiset α} {k : ℕ} (hk : k ≤ Multiset.card t) :
    ∃ w, w ≤ t ∧ Multiset.card w = k := by
  have hpow : Multiset.powersetCard k t ≠ 0 := by
    intro h0
    have hc := Multiset.card_powersetCard k t
    rw [h0, Multiset.card_zero] at hc
    exact absurd (Nat.choose_pos hk) (by omega)
  obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hpow
  exact ⟨w, (Multiset.mem_powersetCard.1 hw).1, (Multiset.mem_powersetCard.1 hw).2⟩

/-- **A repeat in the multiset produces a repeat among its sub-multisets of a given size.** -/
theorem not_nodup_powersetCard_of_not_nodup {s : Multiset α} {m : ℕ} (hm : 0 < m)
    (hms : m < Multiset.card s) (hs : ¬ s.Nodup) :
    ¬ (Multiset.powersetCard m s).Nodup := by
  obtain ⟨a, ha⟩ : ∃ a, 2 ≤ Multiset.count a s := by
    by_contra hcon
    push Not at hcon
    exact hs (Multiset.nodup_iff_count_le_one.2 fun a => by have := hcon a; omega)
  obtain ⟨t, ht⟩ : ∃ t, s = Multiset.replicate 2 a + t :=
    Multiset.le_iff_exists_add.1 (Multiset.le_count_iff_replicate_le.1 ha)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hcards : Multiset.card s = 2 + Multiset.card t := by
    rw [ht, Multiset.card_add, Multiset.card_replicate]
  obtain ⟨w, hwle, hwcard⟩ := exists_le_card_eq (t := t) (k := k) (by omega)
  have hcons : s = a ::ₘ (a ::ₘ t) := by
    rw [ht]
    simp [Multiset.replicate_succ]
  intro hnodup
  rw [hcons, Multiset.powersetCard_cons, Multiset.nodup_add] at hnodup
  have h1 : (a ::ₘ w) ∈ Multiset.powersetCard (k + 1) (a ::ₘ t) := by
    refine Multiset.mem_powersetCard.2 ⟨Multiset.cons_le_cons a hwle, ?_⟩
    rw [Multiset.card_cons, hwcard]
  have h2 : (a ::ₘ w) ∈ Multiset.map (Multiset.cons a) (Multiset.powersetCard k (a ::ₘ t)) := by
    refine Multiset.mem_map.2 ⟨w, Multiset.mem_powersetCard.2 ⟨?_, hwcard⟩, rfl⟩
    exact le_trans hwle (Multiset.le_cons_self t a)
  have hle := hnodup.2.2 (Multiset.singleton_le.2 h1) (Multiset.singleton_le.2 h2)
  rw [le_bot_iff] at hle
  simp at hle

/-- **The sub-multisets of a fixed intermediate size are distinct exactly when the multiset has no
repeats.** -/
theorem nodup_powersetCard_iff {s : Multiset α} {m : ℕ} (hm : 0 < m)
    (hms : m < Multiset.card s) :
    (Multiset.powersetCard m s).Nodup ↔ s.Nodup := by
  refine ⟨fun h => ?_, fun h => h.powersetCard⟩
  by_contra hs
  exact not_nodup_powersetCard_of_not_nodup hm hms hs h

end GaloisForLFunctions.HTGeometry
