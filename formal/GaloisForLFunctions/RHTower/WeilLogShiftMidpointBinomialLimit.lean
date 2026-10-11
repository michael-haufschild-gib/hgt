import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialBound
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticMassLimit

/-! Every quadratic-start midpoint probability approaches the binomial law in l1. -/

open scoped BigOperators
open Filter Topology
noncomputable section
namespace RHTower

theorem tendsto_finiteWeil_midpoint_binomial_error :
    Tendsto (fun r : ℕ =>
      2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have he : Tendsto (fun r : ℕ =>
      Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun r => by positivity) (fun r => le_add_of_nonneg_right (by positivity))
      tendsto_finiteWeil_quadratic_concentration_error
  simpa only [mul_zero] using he.const_mul (2 : ℝ)

/-- No regularity or growth assumption is imposed on the nonnegative offsets. -/
theorem tendsto_finiteWeilCanonicalMixture_midpoint_binomial (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ =>
      ∑ i, |finiteWeilCanonicalMixture r (2 * (r + 1) ^ 2 + t r) (1 / 2) i -
        ((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)|) atTop (𝓝 0) := by
  apply squeeze_zero (fun r => Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun r => finiteWeilCanonicalMixture_midpoint_binomial_bound r _ ?_)
    tendsto_finiteWeil_midpoint_binomial_error
  push_cast
  have ht : (0 : ℝ) ≤ (t r : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht]

end RHTower
