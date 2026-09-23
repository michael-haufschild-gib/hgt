import GaloisForLFunctions.RHTower.Sieve.LinearRangeEstimate
import GaloisForLFunctions.RHTower.Sieve.LinearRangeVariable

/-!
# The linear short-interval mean square over a range

Composing the change of variables with the range estimate: over the starting points
`Y < x ≤ Y(1+ε)^K`,

    ∫ |∑_{x < n ≤ x+L} a_n|² dx ≤ Y(1+ε)^K · K · blockCost L Y ε M₁ M₂ W ,

where `blockCost = 2(M₁·log(1+L/Y) + M₂·2/(π²W)) + 2(εL+1)²·log(1+ε)`.

`M₁` is a bound on `|∑_n a_n n^{2πiw}|²` for `|w| ≤ W` and `M₂` one valid for all `w`; the first is
what a cancellation estimate supplies, the second is the trivial size.  Nothing analytic enters the
composition.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- **The linear short-interval mean square over a range of starting points.** -/
theorem integral_Ioc_normSq_linSum_range_le (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {L Y ε M₁ M₂ W : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hW : 0 < W)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ w ∈ Set.Icc (-W) W, ‖logPoly a s w‖ ^ (2 : ℕ) ≤ M₁)
    (h₂ : ∀ w : ℝ, ‖logPoly a s w‖ ^ (2 : ℕ) ≤ M₂) (K : ℕ) :
    (∫ x in Set.Ioc Y (Y * (1 + ε) ^ K), ‖linSum a s L x‖ ^ (2 : ℕ))
      ≤ (Y * (1 + ε) ^ K) * ((K : ℝ) * blockCost L Y ε M₁ M₂ W) := by
  have hone : (0 : ℝ) < 1 + ε := by linarith
  have hZ0 : (0 : ℝ) < Y * (1 + ε) ^ K := by positivity
  have hYexp : Real.exp (Real.log Y) = Y := Real.exp_log hY
  have hZexp : Real.exp (Real.log (Y * (1 + ε) ^ K)) = Y * (1 + ε) ^ K := Real.exp_log hZ0
  have hstep := integral_Ioc_normSq_linSum_le a s L (Real.log Y) (Real.log (Y * (1 + ε) ^ K))
  rw [hYexp, hZexp] at hstep
  refine le_trans hstep ?_
  have hrange := setIntegral_normSq_linWindowSum_range_le a s hs ha hL hY hε hW hM₁ hM₂ h₁ h₂ K
  exact mul_le_mul_of_nonneg_left hrange hZ0.le

end RHTower.Sieve
