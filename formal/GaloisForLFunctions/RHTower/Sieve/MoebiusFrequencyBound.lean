import GaloisForLFunctions.RHTower.Sieve.MoebiusDiscreteMeanSquare
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistSharpLittleO

/-!
# Discharging the frequency hypothesis

The mean-square bound of `MoebiusDiscreteMeanSquare.lean` has one arithmetic hypothesis: a bound on
the twisted Möbius sum for `|w| ≤ W`.  The twisted contour argument bounds that sum for
`5 + 4|τ| ≤ contourParam`, and the two ranges match under `τ = -2πw`: `|τ| = 2π|w|`, so
`5 + 4|τ| = 5 + 8π|w|`, and the admissible `W` is `(contourParam - 5)/(8π)`.

The index set is `(range M).erase 0`, which changes nothing since the twisted coefficient vanishes at
`0`.
-/

namespace RHTower.Sieve

open Finset

/-- Deleting `0` from the index set does not change the twisted sum. -/
theorem sum_moebiusTwist_erase (τ : ℝ) (M : ℕ) :
    (∑ n ∈ (Finset.range M).erase 0, moebiusTwist τ n)
      = ∑ n ∈ Finset.range M, moebiusTwist τ n := by
  classical
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · rw [← Finset.sum_erase (Finset.range M) (moebiusTwist_zero τ)]

/-- The twist of a frequency in the band is admissible for the contour. -/
theorem admissible_of_abs_le {W C w : ℝ} (hW : 8 * Real.pi * W + 5 ≤ C) (hw : |w| ≤ W) :
    5 + 4 * |(-(2 * Real.pi * w))| ≤ C := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have habs : |(-(2 * Real.pi * w))| = 2 * Real.pi * |w| := by
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [habs]
  nlinarith [hw, hpi, abs_nonneg w]

/-- **The frequency hypothesis, discharged from the twisted contour bound.** -/
theorem normSq_sum_moebiusTwist_le (M : ℕ) {N B W C : ℝ} (hN : 0 < N)
    (hbound : ∀ τ : ℝ, 5 + 4 * |τ| ≤ C →
      ‖∑ n ∈ Finset.range M, moebiusTwist τ n‖ / N ≤ B)
    (hW : 8 * Real.pi * W + 5 ≤ C) :
    ∀ w : ℝ, |w| ≤ W →
      ‖∑ n ∈ (Finset.range M).erase 0, moebiusTwist (-(2 * Real.pi * w)) n‖ ^ 2
        ≤ (B * N) ^ 2 := by
  intro w hw
  rw [sum_moebiusTwist_erase]
  have hadm := admissible_of_abs_le hW hw
  have h := hbound (-(2 * Real.pi * w)) hadm
  rw [div_le_iff₀ hN] at h
  have h0 : (0 : ℝ) ≤ ‖∑ n ∈ Finset.range M, moebiusTwist (-(2 * Real.pi * w)) n‖ :=
    norm_nonneg _
  nlinarith [h, h0, hN.le]

end RHTower.Sieve
