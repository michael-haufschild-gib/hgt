import GaloisForLFunctions.WindowedLandauTheory.SubspaceCounting.GoodOrbitIntervalTileCondition

/-! Disjoint intervals and alternating cells in the orbit tile condition. -/

open Finset WindowedLandauTheory.G0

namespace UpperTheory.BernoulliSumsFrobeniusOrbits

def tile (r u s : ℕ) : Finset ℕ :=
  Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u))

theorem cell_subset {r u s c : ℕ} (hc : c ≤ 6 * r + 1) : cell r u s c ⊆ tile r u s := by
  intro x hx
  simp only [cell, tile, mem_Ico] at hx ⊢
  have : c * u ≤ (6 * r + 1) * u := Nat.mul_le_mul_right u hc
  constructor <;> nlinarith [hx.1, hx.2]

theorem cell_card {r u s c : ℕ} (hc : 1 ≤ c) : (cell r u s c).card = u := by
  unfold cell
  rw [Nat.card_Ico]
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (c + 1) * u = c * u + u by ring, ← add_assoc, Nat.add_sub_cancel_left]

theorem ico_disjoint {a m i j : ℕ} (hij : i ≠ j) :
    Disjoint (Finset.Ico (a + i * m) (a + (i + 1) * m)) (Finset.Ico (a + j * m) (a + (j + 1) * m)) := by
  rw [disjoint_left]
  intro x hx hx'
  simp only [mem_Ico] at hx hx'
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have : (i + 1) * m ≤ j * m := Nat.mul_le_mul_right m h
    omega
  · have : (j + 1) * m ≤ i * m := Nat.mul_le_mul_right m h
    omega

theorem tile_disjoint {r u s s' : ℕ} (h : s ≠ s') : Disjoint (tile r u s) (tile r u s') := by
  have := ico_disjoint (a := 0) (m := (6 * r + 1) * u) h
  simpa [tile] using this

theorem prod_alternate (a b : ℝ) (m : ℕ) :
    ∏ c ∈ Finset.range (2 * m + 1), (if Even c then a else b) = a ^ (m + 1) * b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    have h2 : Even (2 * m + 1 + 1) := ⟨m + 1, by ring⟩
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      if_neg h1, if_pos h2]
    ring

theorem marked_congr {T T' : Finset ℕ} {r u s : ℕ} (h : T ∩ tile r u s = T' ∩ tile r u s)
    (hM : Marked T r u s) : Marked T' r u s := by
  intro c hc1 hc2
  have hsub := cell_subset (r := r) (u := u) (s := s) hc2
  have e : T ∩ cell r u s c = T' ∩ cell r u s c := by
    rw [← inter_eq_right.mpr hsub, ← inter_assoc, ← inter_assoc, h]
  rw [← e]
  exact hM c hc1 hc2

end UpperTheory.BernoulliSumsFrobeniusOrbits
