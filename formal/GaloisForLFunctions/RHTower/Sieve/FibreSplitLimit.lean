import GaloisForLFunctions.RHTower.Sieve.FibreSumSplit
import GaloisForLFunctions.RHTower.Sieve.PairFibreMeanSquare

/-!
# The averaged mean square from the two halves

At the level of limits, the top-level split says: if both the part of the fibre sums away from the
discarded set and the size of the discarded part are `o(h²√x)`, then the averaged fibre mean square
vanishes — which is the Route E cards' short-interval input.

The discarded set is an arbitrary family of finite sets, one for each scale.
-/

namespace RHTower.Sieve

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- **The averaged mean square from the two halves of the split.** -/
theorem averagedMeanSquare_of_split {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {hh : ℝ → ℝ}
    (T : ℝ → Finset ℕ) (hh0 : ∀ᶠ x in atTop, 0 < hh x)
    (hmain : Tendsto (fun x : ℝ =>
        (2 * ∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a \ T x, f b) ^ 2)
          / (hh x ^ 2 * Real.sqrt x)) atTop (𝓝 0))
    (hrough : Tendsto (fun x : ℝ =>
        (2 * ∑ a ∈ outerBlock x (hh x),
            (((innerFibre x (hh x) a ∩ T x).card : ℕ) : ℝ) ^ 2)
          / (hh x ^ 2 * Real.sqrt x)) atTop (𝓝 0)) :
    AveragedMeanSquare f hh := by
  rw [AveragedMeanSquare]
  have hsum := hmain.add hrough
  rw [add_zero] at hsum
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [hh0, Filter.eventually_gt_atTop (0 : ℝ)] with x hx1 hx2
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx2
  have hden : (0 : ℝ) < hh x ^ 2 * Real.sqrt x := by positivity
  have hnum0 : (0 : ℝ)
      ≤ ∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a, f b) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcomb : (2 * ∑ a ∈ outerBlock x (hh x),
        (∑ b ∈ innerFibre x (hh x) a \ T x, f b) ^ 2) / (hh x ^ 2 * Real.sqrt x)
      + (2 * ∑ a ∈ outerBlock x (hh x),
          (((innerFibre x (hh x) a ∩ T x).card : ℕ) : ℝ) ^ 2) / (hh x ^ 2 * Real.sqrt x)
      = ((2 * ∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a \ T x, f b) ^ 2)
          + 2 * ∑ a ∈ outerBlock x (hh x),
            (((innerFibre x (hh x) a ∩ T x).card : ℕ) : ℝ) ^ 2) / (hh x ^ 2 * Real.sqrt x) := by
    ring
  rw [hcomb, div_le_div_iff₀ hden hden]
  have hkey := sum_sq_fibreSum_split hf (T x) x (hh x)
  nlinarith [hkey, hden]

end

end RHTower.Sieve
