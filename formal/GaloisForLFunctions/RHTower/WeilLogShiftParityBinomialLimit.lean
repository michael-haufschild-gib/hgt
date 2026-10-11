import GaloisForLFunctions.RHTower.WeilLogShiftParityBinomialBound
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialLimit

/-! Arbitrarily varying probability mixtures and quadratic starts have the same parity model. -/

open scoped BigOperators
open Filter Topology
noncomputable section
namespace RHTower

theorem tendsto_finiteWeil_parity_binomial_error :
    Tendsto (fun r : ℕ =>
      4 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  simpa only [mul_zero, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
    tendsto_finiteWeil_midpoint_binomial_error.const_mul (2 : ℝ)

/-- Both offset and probability-mixture sequences are unrestricted within their natural types. -/
theorem tendsto_finiteWeilCanonicalMixture_binomial (t : ℕ → ℕ)
    (a : ℕ → Set.Icc (0 : ℝ) 1) :
    Tendsto (fun r : ℕ =>
      ∑ i, |finiteWeilCanonicalMixture r (2 * (r + 1) ^ 2 + t r) (a r : ℝ) i -
        finiteWeilBinomialMixture r (a r : ℝ) i|) atTop (𝓝 0) := by
  apply squeeze_zero (fun r => Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun r => finiteWeilCanonicalMixture_binomial_bound r _ (a r : ℝ)
      (a r).property.1 (a r).property.2 ?_)
    tendsto_finiteWeil_parity_binomial_error
  push_cast
  have ht : (0 : ℝ) ≤ (t r : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht]

end RHTower
