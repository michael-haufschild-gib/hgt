import GaloisForLFunctions.RHTower.Sieve.MoebiusFrequencyBound

/-!
# The Möbius short-interval mean square from the twisted contour bound

The final composition: the twisted contour bound is the only input, and it enters through its own
statement — a bound `B` on `‖∑_{n < M} μ(n)n^{-iτ}‖/N` valid for `5 + 4|τ| ≤ C`.  Everything else in

    ∑_{k < K} |∑_{Y+k < n ≤ Y+k+L} μ(n)|²
      ≤ Y(1+ε)^J · J · ( 2((BN)²·log(1+L/Y) + M²·2/(π²W)) + 2(εL+1)²·log(1+ε) )

is elementary and proved.
-/

namespace RHTower.Sieve

open Finset

/-- The block cost is monotone in the global bound. -/
theorem blockCost_mono_right {L Y ε M₁ M₂ M₂' W : ℝ} (hW : 0 < W) (h : M₂ ≤ M₂') :
    blockCost L Y ε M₁ M₂ W ≤ blockCost L Y ε M₁ M₂' W := by
  rw [blockCost, blockCost]
  have hpos : (0 : ℝ) < 2 / (Real.pi ^ (2 : ℕ) * W) := by positivity
  nlinarith [h, hpos]

/-- **The Möbius short-interval mean square, from the twisted contour bound alone.** -/
theorem sum_normSq_moebius_window_le_of_twist (L Y K M J : ℕ) (hM : Y + K + L < M)
    {ε N B W C : ℝ} (hL : 0 < (L : ℝ)) (hY : 0 < (Y : ℝ)) (hε : 0 ≤ ε) (hW : 0 < W)
    (hN : 0 < N)
    (hbound : ∀ τ : ℝ, 5 + 4 * |τ| ≤ C →
      ‖∑ n ∈ Finset.range M, moebiusTwist τ n‖ / N ≤ B)
    (hWC : 8 * Real.pi * W + 5 ≤ C)
    (hJ : (Y : ℝ) + K = (Y : ℝ) * (1 + ε) ^ J) :
    (∑ k ∈ Finset.range K, ‖∑ n ∈ Finset.Ioc (Y + k) (Y + k + L), moebiusC n‖ ^ (2 : ℕ))
      ≤ ((Y : ℝ) * (1 + ε) ^ J)
          * ((J : ℝ) * blockCost (L : ℝ) (Y : ℝ) ε ((B * N) ^ (2 : ℕ)) (((M : ℝ)) ^ (2 : ℕ)) W) := by
  classical
  have hbase := sum_normSq_moebius_window_le L Y K M J hM hL hY hε hW
    (by positivity : (0 : ℝ) ≤ (B * N) ^ (2 : ℕ))
    (normSq_sum_moebiusTwist_le M hN hbound hWC) hJ
  refine le_trans hbase ?_
  have hcard : ((((Finset.range M).erase 0).card : ℝ)) ^ (2 : ℕ) ≤ ((M : ℝ)) ^ (2 : ℕ) := by
    have h : (((Finset.range M).erase 0).card : ℝ) ≤ (M : ℝ) := by
      have := Finset.card_erase_le (s := Finset.range M) (a := 0)
      rw [Finset.card_range] at this
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ (((Finset.range M).erase 0).card : ℝ) := Nat.cast_nonneg _
    nlinarith [h, h0]
  have hmono := blockCost_mono_right (L := (L : ℝ)) (Y := (Y : ℝ)) (ε := ε)
    (M₁ := (B * N) ^ (2 : ℕ)) hW hcard
  have hZ : (0 : ℝ) ≤ (Y : ℝ) * (1 + ε) ^ J := by positivity
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hJ0) hZ

end RHTower.Sieve
