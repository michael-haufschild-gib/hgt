import Mathlib

/-!
# Pairs at bounded distance

The second moment of a set over the fibres is its number of pairs at distance at most `h`.  Each
such pair is determined by its smaller element, their difference, and which of the two is smaller,
so the count is at most twice the sum over differences of the shifted pair counts — the quantity a
two-dimensional sieve controls.
-/

namespace RHTower.Sieve

open Finset

/-- **Pairs at distance at most `h` are counted by their differences.** -/
theorem card_bandPairs_le (A : Finset ℕ) {h : ℝ} :
    ((((A ×ˢ A).filter
        (fun p => ((max p.1 p.2 : ℕ) : ℝ) - ((min p.1 p.2 : ℕ) : ℝ) ≤ h)).card : ℕ) : ℝ)
      ≤ 2 * ∑ d ∈ Finset.range (⌊h⌋₊ + 1),
          (((A.filter (fun m => m + d ∈ A)).card : ℕ) : ℝ) := by
  classical
  set F : Finset (ℕ × ℕ) := (A ×ˢ A).filter
    (fun p => ((max p.1 p.2 : ℕ) : ℝ) - ((min p.1 p.2 : ℕ) : ℝ) ≤ h) with hF
  set B : Finset (ℕ × ℕ) :=
    (Finset.range (⌊h⌋₊ + 1)).biUnion
      (fun d => (A.filter (fun m => m + d ∈ A)).biUnion
        (fun a => ({(a, a + d), (a + d, a)} : Finset (ℕ × ℕ)))) with hB
  have hsub : F ⊆ B := by
    intro p hp
    rw [hF, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hdist⟩ := hp
    set a : ℕ := min p.1 p.2 with ha
    set b : ℕ := max p.1 p.2 with hb
    have hab : a ≤ b := min_le_max
    set d : ℕ := b - a with hd
    have hbd : b = a + d := by omega
    have hdle : d ≤ ⌊h⌋₊ := by
      have hdR : ((d : ℕ) : ℝ) ≤ h := by
        rw [hd, Nat.cast_sub hab]
        exact hdist
      exact Nat.le_floor hdR
    have haA : a ∈ A := by
      rcases le_total p.1 p.2 with hle | hle
      · rw [ha, min_eq_left hle]; exact h1
      · rw [ha, min_eq_right hle]; exact h2
    have hbA : b ∈ A := by
      rcases le_total p.1 p.2 with hle | hle
      · rw [hb, max_eq_right hle]; exact h2
      · rw [hb, max_eq_left hle]; exact h1
    rw [hB, Finset.mem_biUnion]
    refine ⟨d, Finset.mem_range.2 (by omega), ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨a, Finset.mem_filter.2 ⟨haA, by rw [← hbd]; exact hbA⟩, ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases le_total p.1 p.2 with hle | hle
    · left
      have h1' : p.1 = a := by rw [ha, min_eq_left hle]
      have h2' : p.2 = b := by rw [hb, max_eq_right hle]
      rw [← hbd, ← h1', ← h2']
    · right
      have h1' : p.1 = b := by rw [hb, max_eq_left hle]
      have h2' : p.2 = a := by rw [ha, min_eq_right hle]
      rw [← hbd, ← h1', ← h2']
  have hcard : F.card ≤ B.card := Finset.card_le_card hsub
  have hBcard : B.card
      ≤ ∑ d ∈ Finset.range (⌊h⌋₊ + 1), 2 * (A.filter (fun m => m + d ∈ A)).card := by
    refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum fun d _ => ?_)
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum fun a _ => Finset.card_insert_le _ _) ?_
    simp only [Finset.card_singleton]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hchain : (F.card : ℝ)
      ≤ ((∑ d ∈ Finset.range (⌊h⌋₊ + 1), 2 * (A.filter (fun m => m + d ∈ A)).card : ℕ) : ℝ) := by
    exact_mod_cast le_trans hcard hBcard
  refine hchain.trans (le_of_eq ?_)
  push_cast
  rw [Finset.mul_sum]

end RHTower.Sieve
