import GaloisForLFunctions.RHTower.WeilLogShiftBinomialMixture
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialBound

/-! Every probability mixture in the canonical fiber has its matching binomial approximation. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilCanonicalMixture_binomial_bound (r k : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    (∑ i, |finiteWeilCanonicalMixture r k a i - finiteWeilBinomialMixture r a i|) ≤
      4 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have hi (i : Fin (r + 2)) :
      |finiteWeilCanonicalMixture r k a i - finiteWeilBinomialMixture r a i| ≤
        2 * |finiteWeilCanonicalMixture r k (1 / 2) i -
          ((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)| := by
    have hm := finiteWeilBinomialParity_multiplier_bounds r a ha ha1 i
    rw [finiteWeilCanonicalMixture_parity_factor, finiteWeilBinomialMixture_parity_factor,
      ← mul_sub, abs_mul, abs_of_nonneg hm.1]
    exact mul_le_mul_of_nonneg_right hm.2 (abs_nonneg _)
  calc
    _ ≤ ∑ i, 2 * |finiteWeilCanonicalMixture r k (1 / 2) i -
        ((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)| :=
      Finset.sum_le_sum fun i _ => hi i
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      have h := finiteWeilCanonicalMixture_midpoint_binomial_bound r k hwidth
      nlinarith only [h]

end RHTower
