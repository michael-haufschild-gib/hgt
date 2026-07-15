import GaloisForLFunctions.RHTower.GaussComponentVerticalMagnitude

namespace RHTower

open Complex Filter Topology

noncomputable section

/-- Raising a Gauss-component magnitude to its critical integral power gives the universal
linear normalization `2π`. -/
theorem gaussComponentVerticalMagnitude_pow_mul_tendsto
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    Tendsto (fun t : ℝ =>
      (gaussComponentVerticalMagnitude k t) ^ (2 * m) * t)
      atTop (nhds (2 * Real.pi)) := by
  have hn : 2 * m ≠ 0 := by omega
  have hmain := (gaussComponentVerticalMagnitude_mul_rpow_tendsto hm k).pow (2 * m)
  have hconstant :
      ((2 * Real.pi) ^ gaussComponentDelta m) ^ (2 * m) = 2 * Real.pi := by
    rw [gaussComponentDelta]
    convert Real.rpow_inv_natCast_pow (by positivity : 0 ≤ 2 * Real.pi) hn using 1
    all_goals norm_num [one_div, Nat.cast_mul]
  rw [hconstant] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htpower : (t ^ gaussComponentDelta m) ^ (2 * m) = t := by
    rw [gaussComponentDelta]
    convert Real.rpow_inv_natCast_pow ht.le hn using 1
    all_goals norm_num [one_div, Nat.cast_mul]
  rw [mul_pow, htpower]

end

end RHTower
