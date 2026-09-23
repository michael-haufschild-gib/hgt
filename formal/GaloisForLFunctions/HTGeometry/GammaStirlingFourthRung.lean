import GaloisForLFunctions.HTGeometry.GammaStirlingThirdRung

/-!
# The fourth rung: the coefficient `−1/120`

The quintic contributions of the one-step difference are `−1/5`, `+1/2`, `−1/3`, summing to
`−1/30`, so this rung is *not* free: a `1/z⁴` term is needed, and its coefficient is forced by
`−1/30 − 4 c₄ = 0`, i.e. `c₄ = −1/120`, matching the classical
`ψ(z) ∼ log z − 1/(2z) − 1/(12 z²) + 1/(120 z⁴)`.

Every remainder is again an explicit rational function of `u = 1/z`; the Taylor bound and the
telescope are the order-uniform ones.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-- The fourth-rung Stirling defect. -/
def digammaStirlingDefectFour (z : ℂ) : ℂ :=
  Complex.digamma z - Complex.log z + 1 / (2 * z) + 1 / (12 * z ^ (2 : ℕ)) - 1 / (120 * z ^ (4 : ℕ))

theorem digammaStirlingDefectFour_step (z : ℂ) :
    digammaStirlingDefectFour (z + 1) - digammaStirlingDefectFour z
      = (digammaStirlingDefectTwo (z + 1) - digammaStirlingDefectTwo z)
        - (1 / (120 * (z + 1) ^ (4 : ℕ)) - 1 / (120 * z ^ (4 : ℕ))) := by
  rw [digammaStirlingDefectFour, digammaStirlingDefectFour, digammaStirlingDefectTwo,
    digammaStirlingDefectTwo]
  ring

set_option maxHeartbeats 2000000 in
/-- **The fourth-rung gain.** -/
theorem norm_digammaStirlingDefectFour_step_le {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖digammaStirlingDefectFour (z + 1) - digammaStirlingDefectFour z‖ ≤ 9 / ‖z‖ ^ (6 : ℕ) := by
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
    have hzz : ‖(1 : ℂ) + u‖ = 0 := by rw [h]; simp
    rw [hzz] at hulow
    linarith
  have hu6 : ‖u‖ ^ (6 : ℕ) = 1 / ‖z‖ ^ (6 : ℕ) := by rw [hunorm, div_pow, one_pow]
  have hA : ‖u - Complex.log (1 + u) - u ^ (2 : ℕ) / 2 + u ^ (3 : ℕ) / 3 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 5‖
      ≤ ‖u‖ ^ (6 : ℕ) := by
    have hbase := norm_log_one_add_sub_taylor_le' (u := u) huhalf (n := 6) (by omega)
    have hsum : ∑ j ∈ Finset.range 6, (-1 : ℂ) ^ (j + 1) * u ^ j / (j : ℂ)
        = u - u ^ (2 : ℕ) / 2 + u ^ (3 : ℕ) / 3 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 5 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
      ring
    rw [hsum] at hbase
    have hid : u - Complex.log (1 + u) - u ^ (2 : ℕ) / 2 + u ^ (3 : ℕ) / 3 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 5
        = -(Complex.log (1 + u) - (u - u ^ (2 : ℕ) / 2 + u ^ (3 : ℕ) / 3 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 5)) := by
      ring
    rw [hid, norm_neg]
    exact hbase
  have hB : ‖-(1 / (2 * z * (z + 1))) + u ^ (2 : ℕ) / 2 - u ^ (3 : ℕ) / 2 + u ^ (4 : ℕ) / 2 - u ^ (5 : ℕ) / 2‖
      ≤ ‖u‖ ^ (6 : ℕ) := by
    have hid : -(1 / (2 * z * (z + 1))) + u ^ (2 : ℕ) / 2 - u ^ (3 : ℕ) / 2 + u ^ (4 : ℕ) / 2 - u ^ (5 : ℕ) / 2
        = -(u ^ (6 : ℕ) / (2 * (1 + u))) := by
      rw [hudef]
      field_simp
      ring
    rw [hid, norm_neg, norm_div, norm_mul, norm_pow]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n, div_le_iff₀ (by positivity)]
    nlinarith [hulow, pow_nonneg (norm_nonneg u) 6]
  have hC : ‖(1 / (12 * (z + 1) ^ (2 : ℕ)) - 1 / (12 * z ^ (2 : ℕ))) + u ^ (3 : ℕ) / 6 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 3‖
      ≤ 3 * ‖u‖ ^ (6 : ℕ) := by
    have hid : (1 / (12 * (z + 1) ^ (2 : ℕ)) - 1 / (12 * z ^ (2 : ℕ))) + u ^ (3 : ℕ) / 6 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 3
        = (u ^ (6 : ℕ) * (5 + 4 * u)) / (12 * (1 + u) ^ (2 : ℕ)) := by
      rw [hudef]
      field_simp
      ring
    rw [hid, norm_div, norm_mul, norm_pow, norm_mul, norm_pow]
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h12]
    have hnum : ‖(5 : ℂ) + 4 * u‖ ≤ 7 := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul]
      have h5 : ‖(5 : ℂ)‖ = 5 := by norm_num
      have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
      rw [h5, h4]
      linarith [huhalf]
    have hden : (3 : ℝ) ≤ 12 * ‖(1 : ℂ) + u‖ ^ (2 : ℕ) := by
      nlinarith [hulow, norm_nonneg ((1 : ℂ) + u)]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hnum, hden, pow_nonneg (norm_nonneg u) 6, norm_nonneg ((5 : ℂ) + 4 * u)]
  have hE : ‖-(1 / (120 * (z + 1) ^ (4 : ℕ)) - 1 / (120 * z ^ (4 : ℕ))) - u ^ (5 : ℕ) / 30‖ ≤ 4 * ‖u‖ ^ (6 : ℕ) := by
    have hid : -(1 / (120 * (z + 1) ^ (4 : ℕ)) - 1 / (120 * z ^ (4 : ℕ))) - u ^ (5 : ℕ) / 30
        = -((u ^ (6 : ℕ) * (10 + 20 * u + 15 * u ^ (2 : ℕ) + 4 * u ^ (3 : ℕ))) / (120 * (1 + u) ^ (4 : ℕ))) := by
      rw [hudef]
      field_simp
      ring
    rw [hid, norm_neg, norm_div, norm_mul, norm_pow, norm_mul, norm_pow]
    have h120 : ‖(120 : ℂ)‖ = 120 := by norm_num
    rw [h120]
    have hnum : ‖(10 : ℂ) + 20 * u + 15 * u ^ (2 : ℕ) + 4 * u ^ (3 : ℕ)‖ ≤ 25 := by
      have hstep : ‖(10 : ℂ) + 20 * u + 15 * u ^ (2 : ℕ) + 4 * u ^ (3 : ℕ)‖
          ≤ ‖(10 : ℂ) + 20 * u + 15 * u ^ (2 : ℕ)‖ + ‖(4 : ℂ) * u ^ (3 : ℕ)‖ := norm_add_le _ _
      have hstep2 : ‖(10 : ℂ) + 20 * u + 15 * u ^ (2 : ℕ)‖
          ≤ ‖(10 : ℂ) + 20 * u‖ + ‖(15 : ℂ) * u ^ (2 : ℕ)‖ := norm_add_le _ _
      have hstep3 : ‖(10 : ℂ) + 20 * u‖ ≤ ‖(10 : ℂ)‖ + ‖(20 : ℂ) * u‖ := norm_add_le _ _
      rw [norm_mul, norm_pow] at hstep
      rw [norm_mul, norm_pow] at hstep2
      rw [norm_mul] at hstep3
      have h10 : ‖(10 : ℂ)‖ = 10 := by norm_num
      have h20 : ‖(20 : ℂ)‖ = 20 := by norm_num
      have h15 : ‖(15 : ℂ)‖ = 15 := by norm_num
      have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
      rw [h10, h20] at hstep3
      rw [h15] at hstep2
      rw [h4] at hstep
      nlinarith [hstep, hstep2, hstep3, huhalf, norm_nonneg u]
    have hden : (7 : ℝ) ≤ 120 * ‖(1 : ℂ) + u‖ ^ (4 : ℕ) := by
      have h4 : (1 : ℝ) / 16 ≤ ‖(1 : ℂ) + u‖ ^ (4 : ℕ) := by
        have hsq : (1 : ℝ) / 4 ≤ ‖(1 : ℂ) + u‖ ^ (2 : ℕ) := by
          nlinarith [hulow, norm_nonneg ((1 : ℂ) + u)]
        have hstep := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hsq 2
        calc (1 : ℝ) / 16 = ((1 : ℝ) / 4) ^ (2 : ℕ) := by norm_num
          _ ≤ (‖(1 : ℂ) + u‖ ^ (2 : ℕ)) ^ (2 : ℕ) := hstep
          _ = ‖(1 : ℂ) + u‖ ^ (4 : ℕ) := by ring
      linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hnum, hden, pow_nonneg (norm_nonneg u) 6,
      norm_nonneg ((10 : ℂ) + 20 * u + 15 * u ^ (2 : ℕ) + 4 * u ^ (3 : ℕ))]
  rw [digammaStirlingDefectFour_step z, digammaStirlingDefectTwo_step hz]
  have hsplit : ((1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1)))
        + (1 / (12 * (z + 1) ^ (2 : ℕ)) - 1 / (12 * z ^ (2 : ℕ))))
      - (1 / (120 * (z + 1) ^ (4 : ℕ)) - 1 / (120 * z ^ (4 : ℕ)))
      = (u - Complex.log (1 + u) - u ^ (2 : ℕ) / 2 + u ^ (3 : ℕ) / 3 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 5)
        + (-(1 / (2 * z * (z + 1))) + u ^ (2 : ℕ) / 2 - u ^ (3 : ℕ) / 2 + u ^ (4 : ℕ) / 2 - u ^ (5 : ℕ) / 2)
        + ((1 / (12 * (z + 1) ^ (2 : ℕ)) - 1 / (12 * z ^ (2 : ℕ))) + u ^ (3 : ℕ) / 6 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 3)
        + (-(1 / (120 * (z + 1) ^ (4 : ℕ)) - 1 / (120 * z ^ (4 : ℕ))) - u ^ (5 : ℕ) / 30) := by
    rw [hudef]
    ring
  rw [hsplit]
  have htotal : ‖(u - Complex.log (1 + u) - u ^ (2 : ℕ) / 2 + u ^ (3 : ℕ) / 3 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 5)
      + (-(1 / (2 * z * (z + 1))) + u ^ (2 : ℕ) / 2 - u ^ (3 : ℕ) / 2 + u ^ (4 : ℕ) / 2 - u ^ (5 : ℕ) / 2)
      + ((1 / (12 * (z + 1) ^ (2 : ℕ)) - 1 / (12 * z ^ (2 : ℕ))) + u ^ (3 : ℕ) / 6 - u ^ (4 : ℕ) / 4 + u ^ (5 : ℕ) / 3)
      + (-(1 / (120 * (z + 1) ^ (4 : ℕ)) - 1 / (120 * z ^ (4 : ℕ))) - u ^ (5 : ℕ) / 30)‖
      ≤ ‖u‖ ^ (6 : ℕ) + ‖u‖ ^ (6 : ℕ) + 3 * ‖u‖ ^ (6 : ℕ) + 4 * ‖u‖ ^ (6 : ℕ) := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ hE
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hA hB)) hC
  refine le_trans htotal (le_of_eq ?_)
  rw [hu6]
  ring

set_option maxHeartbeats 1000000 in
theorem tendsto_digammaStirlingDefectFour_shift_zero {z : ℂ} (hz : 0 ≤ z.re) :
    Tendsto (fun N : ℕ => digammaStirlingDefectFour (z + (N : ℂ))) atTop (nhds 0) := by
  have hbase := tendsto_digammaStirlingDefectTwo_shift_zero hz
  have hnormlow : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ ‖z + (N : ℂ)‖ := by
    intro N hN
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.add_re, Complex.natCast_re, le_abs]
    left
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have htail : Tendsto (fun N : ℕ => (1 : ℂ) / (120 * (z + (N : ℂ)) ^ (4 : ℕ))) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlow := hnormlow N hN
    rw [norm_div, norm_one, norm_mul, norm_pow]
    have h120 : ‖(120 : ℂ)‖ = 120 := by norm_num
    rw [h120]
    have hp : (0 : ℝ) < ‖z + (N : ℂ)‖ := by linarith
    rw [div_le_div_iff₀ (by positivity) hNpos]
    have h4 : (N : ℝ) ≤ ‖z + (N : ℂ)‖ ^ (4 : ℕ) := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (N : ℝ) ^ (4 : ℕ) := pow_le_pow_right₀ hN1 (by omega)
        _ ≤ ‖z + (N : ℂ)‖ ^ (4 : ℕ) := pow_le_pow_left₀ hNpos.le hlow 4
    linarith
  have hsum := hbase.sub htail
  rw [sub_zero] at hsum
  refine hsum.congr fun N => ?_
  rw [digammaStirlingDefectTwo, digammaStirlingDefectFour]

set_option maxHeartbeats 1000000 in
/-- **The fourth-rung Stirling bound.**
`ψ(z) = log z − 1/(2z) − 1/(12 z²) + 1/(120 z⁴) + O(|z|⁻⁵)`. -/
theorem norm_digammaStirlingDefectFour_le {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖digammaStirlingDefectFour z‖ ≤ 27 / ‖z‖ ^ (5 : ℕ) := by
  have h := norm_le_of_step_bound (N := 4) (K := 9) (by norm_num)
    (fun w hw hw2 => norm_digammaStirlingDefectFour_step_le hw hw2) hz h2
    (tendsto_digammaStirlingDefectFour_shift_zero hz.le)
  norm_num at h
  exact h

end

end GaloisForLFunctions.HTGeometry
