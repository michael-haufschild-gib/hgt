import GaloisForLFunctions.HTGeometry.ComplexLogTaylorUniform

/-!
# The third rung is free: the `1/z³` coefficient of `ψ` vanishes

The classical Stirling expansion of `ψ` has no odd terms beyond `−1/(2z)`, and that shows up here as
an *exact* cancellation: with the same defect `g₂(z) = ψ(z) − log z + 1/(2z) + 1/(12 z²)`, the
quartic contributions of the one-step difference,

```text
u − log(1+u)             →  +u⁴/4
−1/(2z(z+1))             →  −u⁴/2
(1/12)(1/(z+1)² − 1/z²)  →  +u⁴/4,
```

sum to `1/4 − 1/2 + 1/4 = 0` as well.  So no new coefficient is needed, the one-step difference is
`O(‖z‖⁻⁵)`, and the telescope upgrades the second-rung bound by one order:

```text
ψ(z) = log z − 1/(2z) − 1/(12 z²) + O(|z|⁻⁴).
```

With `norm_log_one_add_sub_taylor_le'` and `norm_le_of_step_bound` both order-uniform, the only work
is the exact algebra of the three remainders.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **The third-rung gain**: no `1/z³` coefficient is needed. -/
theorem norm_digammaStirlingDefectTwo_step_le' {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖digammaStirlingDefectTwo (z + 1) - digammaStirlingDefectTwo z‖ ≤ 4 / ‖z‖ ^ 5 := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hzpos
    simp at hzpos
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre : (z + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at hre
    linarith
  set u : ℂ := 1 / z with hudef
  have hunorm : ‖u‖ = 1 / ‖z‖ := by rw [hudef, norm_div, norm_one]
  have huhalf : ‖u‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_div_iff₀ hzpos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hulow : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) + u‖ := by
    have hb := norm_sub_le ((1 : ℂ) + u) u
    rw [add_sub_cancel_right, norm_one] at hb
    linarith [huhalf]
  have hune : (1 : ℂ) + u ≠ 0 := by
    intro h
    have hz : ‖(1 : ℂ) + u‖ = 0 := by rw [h]; simp
    rw [hz] at hulow
    linarith
  have hu5 : ‖u‖ ^ 5 = 1 / ‖z‖ ^ 5 := by rw [hunorm, div_pow, one_pow]
  -- the three exact remainders
  have hE1 : ‖u - Complex.log (1 + u) - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4‖ ≤ ‖u‖ ^ 5 := by
    have hbase := norm_log_one_add_sub_taylor_le' (u := u) huhalf (n := 5) (by omega)
    have hsum : ∑ j ∈ Finset.range 5, (-1 : ℂ) ^ (j + 1) * u ^ j / (j : ℂ)
        = u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
      ring
    rw [hsum] at hbase
    have hid : u - Complex.log (1 + u) - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4
        = -(Complex.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4)) := by ring
    rw [hid, norm_neg]
    exact hbase
  have hE2 : ‖-(1 / (2 * z * (z + 1))) + u ^ 2 / 2 - u ^ 3 / 2 + u ^ 4 / 2‖ ≤ ‖u‖ ^ 5 := by
    have hid : -(1 / (2 * z * (z + 1))) + u ^ 2 / 2 - u ^ 3 / 2 + u ^ 4 / 2
        = u ^ 5 / (2 * (1 + u)) := by
      rw [hudef]
      field_simp
      ring
    rw [hid, norm_div, norm_mul, norm_pow]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hulow, pow_nonneg (norm_nonneg u) 5]
  have hE3 : ‖(1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2)) + u ^ 3 / 6 - u ^ 4 / 4‖
      ≤ 2 * ‖u‖ ^ 5 := by
    have hid : (1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2)) + u ^ 3 / 6 - u ^ 4 / 4
        = -(u ^ 5 * (4 + 3 * u)) / (12 * (1 + u) ^ 2) := by
      rw [hudef]
      field_simp
      ring
    rw [hid, norm_div, norm_neg, norm_mul, norm_pow, norm_mul, norm_pow]
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h12]
    have hnum : ‖(4 : ℂ) + 3 * u‖ ≤ 6 := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul]
      have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
      have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      rw [h4, h3]
      linarith [huhalf]
    have hden : (3 : ℝ) ≤ 12 * ‖(1 : ℂ) + u‖ ^ 2 := by
      nlinarith [hulow, norm_nonneg ((1 : ℂ) + u)]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hnum, hden, pow_nonneg (norm_nonneg u) 5, norm_nonneg ((4 : ℂ) + 3 * u)]
  rw [digammaStirlingDefectTwo_step hz]
  have hsplit : (1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1)))
      + (1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2))
      = (u - Complex.log (1 + u) - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4)
        + (-(1 / (2 * z * (z + 1))) + u ^ 2 / 2 - u ^ 3 / 2 + u ^ 4 / 2)
        + ((1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2)) + u ^ 3 / 6 - u ^ 4 / 4) := by
    rw [hudef]
    ring
  rw [hsplit]
  have htotal : ‖(u - Complex.log (1 + u) - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4)
      + (-(1 / (2 * z * (z + 1))) + u ^ 2 / 2 - u ^ 3 / 2 + u ^ 4 / 2)
      + ((1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2)) + u ^ 3 / 6 - u ^ 4 / 4)‖
      ≤ ‖u‖ ^ 5 + ‖u‖ ^ 5 + 2 * ‖u‖ ^ 5 := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hE1 hE2)) hE3
  refine le_trans htotal (le_of_eq ?_)
  rw [hu5]
  ring

set_option maxHeartbeats 1000000 in
/-- **The third-rung Stirling bound.**  `ψ(z) = log z − 1/(2z) − 1/(12 z²) + O(|z|⁻⁴)`. -/
theorem norm_digammaStirlingDefectTwo_le' {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖digammaStirlingDefectTwo z‖ ≤ 12 / ‖z‖ ^ 4 := by
  have h := norm_le_of_step_bound (N := 3) (K := 4) (by norm_num)
    (fun w hw hw2 => norm_digammaStirlingDefectTwo_step_le' hw hw2) hz h2
    (tendsto_digammaStirlingDefectTwo_shift_zero hz.le)
  norm_num at h
  exact h

end

end GaloisForLFunctions.HTGeometry
