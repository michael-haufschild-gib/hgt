import GaloisForLFunctions.RHTower.Sieve.LinearRangeVariable
import GaloisForLFunctions.RHTower.Sieve.RealWindowVariance

/-!
# The discrete window variance as a set integral

The corpus's real-window sum and the linear window sum of this development are the same object: both
are the sum over `{n < M : x < n ≤ x + L}`.  So the discrete mean square over integer starts is a set
integral of `linSum`:

    ∑_{k < K} |∑_{Y+k < n ≤ Y+k+L} c_n|² = ∫_{(Y, Y+K]} |∑_{x < n ≤ x+L} c_n|² dx .

This is the form in which the bounds of this development apply to the card's mean square.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The linear window sum is the corpus's real window sum. -/
theorem linSum_eq_realWindow (c : ℕ → ℂ) (L M : ℕ) (x : ℝ) :
    linSum c (Finset.range M) ((L : ℕ) : ℝ) x = ∑ n ∈ realWindow x L M, c n := rfl

/-- **The discrete window variance is a set integral of the linear window sum.** -/
theorem sum_normSq_Ioc_eq_setIntegral (c : ℕ → ℂ) (L Y K M : ℕ) (hM : Y + K + L < M) :
    (∑ k ∈ Finset.range K, ‖∑ n ∈ Finset.Ioc (Y + k) (Y + k + L), c n‖ ^ 2)
      = ∫ x in Set.Ioc ((Y : ℝ)) ((Y : ℝ) + K),
          ‖linSum c (Finset.range M) ((L : ℕ) : ℝ) x‖ ^ 2 := by
  rw [← integral_realWindow_eq_sum c L Y K M hM,
    intervalIntegral.integral_of_le (by linarith [Nat.cast_nonneg (α := ℝ) K])]
  exact setIntegral_congr_fun measurableSet_Ioc
    (fun x _ => (linSum_eq_realWindow c L M x).symm ▸ rfl)

end RHTower.Sieve
