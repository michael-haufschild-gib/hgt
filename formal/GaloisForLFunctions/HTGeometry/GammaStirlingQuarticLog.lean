import GaloisForLFunctions.HTGeometry.ArchimedeanPowerIndependence

/-!
# The second rung of the Stirling ladder

The `M = 1` rung removed `log z` and `1/(2z)` from `ψ` and gained one order by the cancellation of
the quadratic parts.  The `M = 2` rung removes `1/(12 z²)` as well: writing
`g₂(z) = ψ(z) − log z + 1/(2z) + 1/(12 z²)`, the one-step difference is

```text
g₂(z+1) − g₂(z) = 1/z − log(1 + 1/z) − 1/(2z(z+1)) + (1/12)(1/(z+1)² − 1/z²),
```

and in the variable `u = 1/z` the three cubic contributions `−u³/3`, `+u³/2`, `−u³/6` cancel
exactly.  The coefficient `1/12` is *forced* by that cancellation — this is the shape of every
higher rung, with the `m`-th coefficient fixed by the order-`u^{m+1}` cancellation.

The quartic Taylor bound for the logarithm is proved as the cubic one was, by dropping four terms
of `Complex.hasSum_taylorSeries_log` and summing the geometric tail.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-! ## The quartic Taylor bound -/

theorem norm_log_one_add_sub_taylor_three_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3)‖ ≤ ‖u‖ ^ 4 := by
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hsum := Complex.hasSum_taylorSeries_log hu1
  have hsummable : Summable (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * u ^ n / (n : ℂ)) := hsum.summable
  have hsplit := hsummable.sum_add_tsum_nat_add 4
  have hlog : Complex.log (1 + u) = ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * u ^ n / (n : ℂ) :=
    hsum.tsum_eq.symm
  have hfirst : ∑ n ∈ Finset.range 4, (-1 : ℂ) ^ (n + 1) * u ^ n / (n : ℂ)
      = u - u ^ 2 / 2 + u ^ 3 / 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    norm_num
    ring
  have htail : Complex.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3)
      = ∑' n : ℕ, (-1 : ℂ) ^ (n + 4 + 1) * u ^ (n + 4) / ((n + 4 : ℕ) : ℂ) := by
    rw [hlog, ← hsplit, hfirst]
    ring
  have hbound : ∀ n : ℕ, ‖(-1 : ℂ) ^ (n + 4 + 1) * u ^ (n + 4) / ((n + 4 : ℕ) : ℂ)‖
      ≤ (‖u‖ ^ 4 / 4) * ‖u‖ ^ n := by
    intro n
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    have hcast : ((n + 4 : ℕ) : ℝ) = (n : ℝ) + 4 := by push_cast; ring
    rw [hcast]
    have hden : (4 : ℝ) ≤ (n : ℝ) + 4 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hnum : ‖u‖ ^ (n + 4) = ‖u‖ ^ 4 * ‖u‖ ^ n := by
      rw [pow_add]
      ring
    rw [hnum, div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 4)]
    have hpos : (0 : ℝ) ≤ ‖u‖ ^ 4 * ‖u‖ ^ n := by positivity
    nlinarith [hpos, hden]
  have hgeo : Summable (fun n : ℕ => (‖u‖ ^ 4 / 4) * ‖u‖ ^ n) :=
    (summable_geometric_of_lt_one hu0 hu1).mul_left _
  have hnormsummable : Summable (fun n : ℕ =>
      ‖(-1 : ℂ) ^ (n + 4 + 1) * u ^ (n + 4) / ((n + 4 : ℕ) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgeo
  rw [htail]
  refine le_trans (norm_tsum_le_tsum_norm hnormsummable) ?_
  refine le_trans (hnormsummable.tsum_le_tsum hbound hgeo) ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hu0 hu1]
  rw [div_mul_eq_mul_div, mul_comm]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [hinv, pow_nonneg hu0 4]

/-! ## The second-rung defect -/

/-- The second-rung Stirling defect: `ψ(z) − log z + 1/(2z) + 1/(12 z²)`. -/
def digammaStirlingDefectTwo (z : ℂ) : ℂ :=
  Complex.digamma z - Complex.log z + 1 / (2 * z) + 1 / (12 * z ^ 2)

theorem digammaStirlingDefectTwo_step {z : ℂ} (hz : 0 < z.re) :
    digammaStirlingDefectTwo (z + 1) - digammaStirlingDefectTwo z
      = (1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1)))
        + (1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2)) := by
  have hstep := digammaStirlingDefect_step hz
  rw [digammaStirlingDefectTwo, digammaStirlingDefectTwo]
  rw [digammaStirlingDefect, digammaStirlingDefect] at hstep
  linear_combination hstep

set_option maxHeartbeats 1000000 in
/-- **The second-rung gain.**  The coefficient `1/12` cancels the cubic term exactly, so the
one-step difference of `g₂` is one further order smaller. -/
theorem norm_digammaStirlingDefectTwo_step_le {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖digammaStirlingDefectTwo (z + 1) - digammaStirlingDefectTwo z‖ ≤ 4 / ‖z‖ ^ 4 := by
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
  have hune : (1 : ℂ) + u ≠ 0 := by
    intro h
    have : ‖(1 : ℂ) + u‖ = 0 := by rw [h]; simp
    have hlow : (1 : ℝ) - ‖u‖ ≤ ‖(1 : ℂ) + u‖ := by
      have hb := norm_sub_le ((1 : ℂ) + u) u
      rw [add_sub_cancel_right, norm_one] at hb
      linarith
    rw [this] at hlow
    linarith [huhalf]
  have hulow : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) + u‖ := by
    have hb := norm_sub_le ((1 : ℂ) + u) u
    rw [add_sub_cancel_right, norm_one] at hb
    linarith [huhalf]
  have hu4 : ‖u‖ ^ 4 = 1 / ‖z‖ ^ 4 := by rw [hunorm, div_pow, one_pow]
  -- the three pieces
  have hE1 : ‖u - Complex.log (1 + u) - u ^ 2 / 2 + u ^ 3 / 3‖ ≤ ‖u‖ ^ 4 := by
    have hbase := norm_log_one_add_sub_taylor_three_le huhalf
    have hid : u - Complex.log (1 + u) - u ^ 2 / 2 + u ^ 3 / 3
        = -(Complex.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3)) := by ring
    rw [hid, norm_neg]
    exact hbase
  have hE2 : ‖-(1 / (2 * z * (z + 1))) + u ^ 2 / 2 - u ^ 3 / 2‖ ≤ ‖u‖ ^ 4 := by
    have hid : -(1 / (2 * z * (z + 1))) + u ^ 2 / 2 - u ^ 3 / 2
        = -(u ^ 4 / (2 * (1 + u))) := by
      rw [hudef]
      field_simp
      ring
    rw [hid, norm_neg, norm_div, norm_mul, norm_pow]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hulow, pow_nonneg (norm_nonneg u) 4]
  have hE3 : ‖(1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2)) + u ^ 3 / 6‖ ≤ 2 * ‖u‖ ^ 4 := by
    have hid : (1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2)) + u ^ 3 / 6
        = (u ^ 4 * (3 + 2 * u)) / (12 * (1 + u) ^ 2) := by
      rw [hudef]
      field_simp
      ring
    rw [hid, norm_div, norm_mul, norm_pow, norm_mul, norm_pow]
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h12]
    have hnum : ‖(3 : ℂ) + 2 * u‖ ≤ 4 := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul]
      have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h3, h2']
      linarith [huhalf]
    have hden : (3 : ℝ) ≤ 12 * ‖(1 : ℂ) + u‖ ^ 2 := by
      nlinarith [hulow, norm_nonneg ((1 : ℂ) + u)]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hnum, hden, pow_nonneg (norm_nonneg u) 4, norm_nonneg ((3 : ℂ) + 2 * u)]
  -- assemble
  rw [digammaStirlingDefectTwo_step hz]
  have hsplit : (1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1)))
      + (1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2))
      = (u - Complex.log (1 + u) - u ^ 2 / 2 + u ^ 3 / 3)
        + (-(1 / (2 * z * (z + 1))) + u ^ 2 / 2 - u ^ 3 / 2)
        + ((1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2)) + u ^ 3 / 6) := by
    rw [hudef]
    ring
  rw [hsplit]
  have htotal : ‖(u - Complex.log (1 + u) - u ^ 2 / 2 + u ^ 3 / 3)
      + (-(1 / (2 * z * (z + 1))) + u ^ 2 / 2 - u ^ 3 / 2)
      + ((1 / (12 * (z + 1) ^ 2) - 1 / (12 * z ^ 2)) + u ^ 3 / 6)‖
      ≤ ‖u‖ ^ 4 + ‖u‖ ^ 4 + 2 * ‖u‖ ^ 4 := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hE1 hE2)) hE3
  refine le_trans htotal (le_of_eq ?_)
  rw [hu4]
  ring

end

end GaloisForLFunctions.HTGeometry
