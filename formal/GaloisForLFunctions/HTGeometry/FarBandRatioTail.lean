import GaloisForLFunctions.HTGeometry.FarBandPowerTail

/-!
# The far-band ratio weight

On the frequency lattice the weight

`c · I / ((1 + |j|)² · |I + j|)`,

restricted to the far band `I < 2|j|`, tends to zero as `I → ∞`.  The two regimes are separated by
comparing `|j|` with `2|I + j|`:

* if `|j| ≤ 2|I + j|` the weight is `O(1/(1 + |j|)²)` on a band escaping to infinity;
* otherwise `|I + j| < I` and the weight is `O(1/(I·|I + j|))`, a near-diagonal harmonic band.

Both regimes vanish, by `tendsto_tsum_far_of_ne_top` and `tendsto_tsum_nearDiagonal_zero`.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions

/-- **The far-band ratio weight vanishes.**  The quadratic case of the general power estimate. -/
theorem tendsto_tsum_farBandRatio_zero {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun I : ℕ => ∑' j : ℤ,
      (if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (c * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ 2 * (((I : ℤ) + j).natAbs : ℝ))) else 0))
      atTop (nhds 0) := by
  have h := tendsto_tsum_farBandPower_zero (c := c) (s := 2) hc (by norm_num)
  refine h.congr fun I => tsum_congr fun j => ?_
  have hpow : (1 + (j.natAbs : ℝ)) ^ (2 : ℝ) = (1 + (j.natAbs : ℝ)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (1 + (j.natAbs : ℝ)) 2]
    norm_num
  by_cases hsupp : I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0
  · rw [if_pos hsupp, if_pos hsupp, hpow]
  · rw [if_neg hsupp, if_neg hsupp]

end GaloisForLFunctions
