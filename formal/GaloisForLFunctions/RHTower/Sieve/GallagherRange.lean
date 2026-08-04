import GaloisForLFunctions.RHTower.Sieve.GallagherSplit
import GaloisForLFunctions.RHTower.Sieve.LogWindowMultiplicative

/-!
# The split bound on a range of positions

The integrand of Gallagher's identity is nonnegative, so the bound over the whole line dominates the
bound over any range of positions:

    ∫_E |∑_{u < log n ≤ u+δ} a_n|² du ≤ M₁·δ + M₂·2/(π²W)

for every `E`.  Since the position `u = log x` corresponds to the multiplicative window
`x < n ≤ x·e^δ`, this is the mean square of a multiplicative short-interval sum over any range of
starting points — the form in which such a bound is used.
-/

namespace RHTower.Sieve

open Complex MeasureTheory FourierTransform Finset

/-- The mean square of a logarithmic window sum is integrable. -/
theorem integrable_normSq_logWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (δ : ℝ) :
    Integrable fun u : ℝ => ‖logWindowSum a s δ u‖ ^ 2 := by
  classical
  have h : Integrable fun u : ℝ => ∑ n ∈ s, ∑ m ∈ s,
      (a n * (starRingEnd ℂ) (a m)).re
        * Set.indicator (logWindow δ n ∩ logWindow δ m) (fun _ => (1 : ℝ)) u :=
    integrable_finsetSum _ fun n _ =>
      integrable_finsetSum _ fun m _ => integrable_indicator_logWindow_inter δ n m _
  exact h.congr (Filter.Eventually.of_forall fun u => (normSq_logWindowSum a s δ u).symm)

/-- **The split bound on any range of positions.** -/
theorem setIntegral_normSq_logWindowSum_le (a : ℕ → ℂ) (s : Finset ℕ) {δ M₁ M₂ W : ℝ}
    (hδ : 0 < δ) (hW : 0 < W) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ w ∈ Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2 ≤ M₁)
    (h₂ : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 ≤ M₂) (E : Set ℝ) :
    (∫ u in E, ‖logWindowSum a s δ u‖ ^ 2) ≤ M₁ * δ + M₂ * (2 / (Real.pi ^ 2 * W)) := by
  have hint := integrable_normSq_logWindowSum a s δ
  have hnn : 0 ≤ᵐ[volume] fun u : ℝ => ‖logWindowSum a s δ u‖ ^ 2 :=
    Filter.Eventually.of_forall fun u => by positivity
  refine le_trans (setIntegral_le_integral hint hnn) ?_
  exact gallagher_split a s hδ hW hM₁ hM₂ h₁ h₂

/-- **The multiplicative short-interval mean square, bounded.**  At `u = log x` the window is
`x < n ≤ x·e^δ`, so this bounds the mean square of the multiplicative short-interval sum over any
range of starting positions. -/
theorem setIntegral_normSq_multiplicative_window_le (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) {δ M₁ M₂ W : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ w ∈ Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2 ≤ M₁)
    (h₂ : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 ≤ M₂) (A B : ℝ) :
    (∫ u in Set.Ioc (Real.log A) (Real.log B),
        ‖∑ n ∈ s.filter (fun n : ℕ =>
          Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u * Real.exp δ), a n‖ ^ 2)
      ≤ M₁ * δ + M₂ * (2 / (Real.pi ^ 2 * W)) := by
  classical
  have hcongr : ∀ u : ℝ,
      ‖∑ n ∈ s.filter (fun n : ℕ =>
          Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u * Real.exp δ), a n‖ ^ 2
        = ‖logWindowSum a s δ u‖ ^ 2 := by
    intro u
    rw [← logWindowSum_log a s hs δ (Real.exp_pos u), Real.log_exp]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun u _ => hcongr u)]
  exact setIntegral_normSq_logWindowSum_le a s hδ hW hM₁ hM₂ h₁ h₂ _

end RHTower.Sieve
