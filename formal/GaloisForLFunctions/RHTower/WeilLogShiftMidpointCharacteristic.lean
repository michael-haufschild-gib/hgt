import GaloisForLFunctions.RHTower.WeilLogShiftBinomialCharacteristic
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialLimit

/-! Total-variation control transfers the binomial Gaussian phase limit to the midpoint law. -/

open scoped BigOperators
open Filter Topology

noncomputable section
namespace RHTower

def finiteWeilCanonicalMidpointCharacteristic (r k : ℕ) (u : ℝ) : ℂ :=
  ∑ j : Fin (r + 2), (finiteWeilCanonicalMixture r k (1 / 2) j : ℂ) *
    finiteWeilPhase (u * (((j : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2))

theorem finiteWeilCanonicalMidpointCharacteristic_binomial_bound (r k : ℕ) (u : ℝ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    ‖finiteWeilCanonicalMidpointCharacteristic r k u - finiteWeilBinomialCharacteristic (r + 1) u‖ ≤
      2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have h := finiteWeilPhase_weight_error
    (finiteWeilCanonicalMixture r k (1 / 2))
    (fun j : Fin (r + 2) => ((r + 1).choose (j : ℕ) : ℝ) / 2 ^ (r + 1))
    (fun j : Fin (r + 2) => u * (((j : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2))
  exact h.trans (finiteWeilCanonicalMixture_midpoint_binomial_bound r k hwidth)

theorem tendsto_finiteWeilCanonicalMidpointCharacteristic_gaussian (t : ℕ → ℕ) (α : ℝ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalMidpointCharacteristic r (2 * (r + 1) ^ 2 + t r)
      (α / Real.sqrt ((r + 1 : ℕ) : ℝ))) atTop (𝓝 ((Real.exp (-(α ^ 2 / 8)) : ℝ) : ℂ)) := by
  apply (tendsto_finiteWeilBinomialCharacteristic_gaussian α).congr_dist
  apply squeeze_zero (g := fun r : ℕ =>
    2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ))) (fun r => dist_nonneg)
  · intro r
    rw [dist_eq_norm, norm_sub_rev]
    apply finiteWeilCanonicalMidpointCharacteristic_binomial_bound
    push_cast
    nlinarith only [(Nat.cast_nonneg (t r) : (0 : ℝ) ≤ t r)]
  · exact tendsto_finiteWeil_midpoint_binomial_error

end RHTower
