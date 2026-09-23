import GaloisForLFunctions.RHTower.Sieve.DiscreteWindowBridge
import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquareRange

/-!
# The discrete Möbius short-interval mean square

Assembling the whole development at the Möbius coefficients: for starting points `Y + k`,
`k < K`, covering the range `Y < x ≤ Y(1+ε)^J`,

    ∑_{k < K} |∑_{Y+k < n ≤ Y+k+L} μ(n)|²
      ≤ Y(1+ε)^J · J · ( 2(M₁·log(1+L/Y) + (#s)²·2/(π²W)) + 2(εL+1)²·log(1+ε) ) ,

the single arithmetic hypothesis being a bound `M₁` on the twisted Möbius sum for `|w| ≤ W`.

The window index set is `(range M).erase 0`, which for positive starting points is the same window as
the corpus's `realWindow`: the value `n = 0` can only enter a window with a negative start.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- For nonnegative starting points, deleting `0` from the index set changes no window. -/
theorem linSum_erase_eq_realWindow (c : ℕ → ℂ) (L M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    linSum c ((Finset.range M).erase 0) ((L : ℕ) : ℝ) x = ∑ n ∈ realWindow x L M, c n := by
  classical
  rw [linSum, realWindow]
  refine Finset.sum_congr ?_ fun n _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
  constructor
  · rintro ⟨⟨-, hn⟩, h1, h2⟩
    exact ⟨hn, h1, h2⟩
  · rintro ⟨hn, h1, h2⟩
    refine ⟨⟨?_, hn⟩, h1, h2⟩
    rintro rfl
    simp only [Nat.cast_zero] at h1
    linarith

/-- **The discrete Möbius short-interval mean square.** -/
theorem sum_normSq_moebius_window_le (L Y K M J : ℕ) (hM : Y + K + L < M)
    {ε M₁ W : ℝ} (hL : 0 < (L : ℝ)) (hY : 0 < (Y : ℝ)) (hε : 0 ≤ ε) (hW : 0 < W)
    (hM₁ : 0 ≤ M₁)
    (h₁ : ∀ w : ℝ, |w| ≤ W →
      ‖∑ n ∈ (Finset.range M).erase 0, moebiusTwist (-(2 * Real.pi * w)) n‖ ^ (2 : ℕ) ≤ M₁)
    (hJ : (Y : ℝ) + K = (Y : ℝ) * (1 + ε) ^ J) :
    (∑ k ∈ Finset.range K, ‖∑ n ∈ Finset.Ioc (Y + k) (Y + k + L), moebiusC n‖ ^ (2 : ℕ))
      ≤ ((Y : ℝ) * (1 + ε) ^ J)
          * ((J : ℝ) * blockCost (L : ℝ) (Y : ℝ) ε M₁
              ((((Finset.range M).erase 0).card : ℝ) ^ (2 : ℕ)) W) := by
  classical
  have hs : ∀ n ∈ (Finset.range M).erase 0, 0 < n := by
    intro n hn
    exact Nat.pos_of_ne_zero (Finset.mem_erase.1 hn).1
  rw [sum_normSq_Ioc_eq_setIntegral moebiusC L Y K M hM]
  have hcongr : (∫ x in Set.Ioc ((Y : ℝ)) ((Y : ℝ) + K),
        ‖linSum moebiusC (Finset.range M) ((L : ℕ) : ℝ) x‖ ^ (2 : ℕ))
      = ∫ x in Set.Ioc ((Y : ℝ)) ((Y : ℝ) + K),
          ‖linSum moebiusC ((Finset.range M).erase 0) ((L : ℕ) : ℝ) x‖ ^ (2 : ℕ) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans hY hx.1)
    rw [linSum_erase_eq_realWindow moebiusC L M hx0, ← linSum_eq_realWindow moebiusC L M x]
  rw [hcongr, hJ]
  exact integral_Ioc_normSq_moebius_range_le ((Finset.range M).erase 0) hs hL hY hε hW hM₁ h₁ J

end RHTower.Sieve
