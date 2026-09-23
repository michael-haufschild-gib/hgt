import GaloisForLFunctions.RHTower.Sieve.WindowStepIntegral

/-!
# The mean square over real starts, stated for the real window

Combining `realWindow_eq_Ioc` with the step-function integral gives the identity in the form the
cited estimates use:

`∫_Y^{Y+K} ‖∑_{x < n ≤ x+L} c_n‖² dx = ∑_{k < K} ‖∑_{Y+k < n ≤ Y+k+L} c_n‖²`.

The cutoff `M` only has to exceed `Y+K+L`, so that every window met on `[Y, Y+K]` fits below it.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **The continuous mean square of the real window is the discrete variance.** -/
theorem integral_realWindow_eq_sum (c : ℕ → ℂ) (L Y K M : ℕ) (hM : Y + K + L < M) :
    ∫ x in (Y : ℝ)..((Y : ℝ) + K), ‖∑ n ∈ realWindow x L M, c n‖ ^ (2 : ℕ)
      = ∑ k ∈ Finset.range K, ‖∑ n ∈ Finset.Ioc (Y + k) (Y + k + L), c n‖ ^ (2 : ℕ) := by
  have hcongr : ∫ x in (Y : ℝ)..((Y : ℝ) + K), ‖∑ n ∈ realWindow x L M, c n‖ ^ (2 : ℕ)
      = ∫ x in (Y : ℝ)..((Y : ℝ) + K), stepWindow c L ⌊x⌋₊ := by
    refine intervalIntegral.integral_congr_uIoo ?_
    intro x hx
    rw [Set.uIoo_of_le (le_add_of_nonneg_right (Nat.cast_nonneg K)), Set.mem_Ioo] at hx
    show ‖∑ n ∈ realWindow x L M, c n‖ ^ (2 : ℕ) = stepWindow c L ⌊x⌋₊
    have hx0 : (0 : ℝ) ≤ x := le_trans (Nat.cast_nonneg Y) (le_of_lt hx.1)
    have hlt : ⌊x⌋₊ < Y + K := by
      refine (Nat.floor_lt hx0).mpr ?_
      have : ((Y + K : ℕ) : ℝ) = (Y : ℝ) + K := by push_cast; ring
      rw [this]
      exact hx.2
    rw [realWindow_eq_Ioc hx0 (by omega), stepWindow]
  rw [hcongr, integral_stepWindow_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [stepWindow]

end RHTower.Sieve
