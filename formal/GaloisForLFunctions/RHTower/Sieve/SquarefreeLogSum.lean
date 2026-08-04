import GaloisForLFunctions.RHTower.Sieve.SquarefreeGlobalCount
import GaloisForLFunctions.RHTower.Sieve.LogSumFromCount

/-!
# The logarithmic mean of the squarefree indicator

The `μ²` instance of `LogSumFromCount.lean`: the squarefree count is `mD + O(√m)`, so

    ∑_{√x < a ≤ 2√x} μ²(a)/a  →  D log 2,      D = 6/π².

This is what turns the main term of the `μ²` bilinear sum into the square of the block mean.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology

theorem squarefreeDensity_nonneg' : 0 ≤ squarefreeDensity := by
  rw [squarefreeDensity_eq]
  positivity

/-- The squarefree counting error, in the general notation. -/
theorem abs_weightErr_moebius_sq_le (m : ℕ) :
    |weightErr (fun n : ℕ => ((moebius n : ℤ) : ℝ) ^ 2) squarefreeDensity m|
      ≤ 2 * Real.sqrt m + 2 := by
  have hbase := abs_sum_moebius_sq_Icc_sub_le m
  rw [weightErr, weightCount]
  linarith [hbase]

/-- **The logarithmic mean of the squarefree indicator over a dyadic block.** -/
theorem tendsto_squarefree_block_log_mean :
    Tendsto (fun u : ℝ => ∑ a ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, ((moebius a : ℤ) : ℝ) ^ 2 / (a : ℝ))
      atTop (𝓝 (squarefreeDensity * Real.log 2)) :=
  tendsto_block_log_mean_of_count squarefreeDensity_nonneg' (by norm_num)
    abs_weightErr_moebius_sq_le

end RHTower.Sieve
