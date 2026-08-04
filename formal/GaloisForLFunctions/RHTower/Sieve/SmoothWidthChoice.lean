import GaloisForLFunctions.RHTower.Sieve.ExpQuadraticDecay

/-!
# The smoothing width

The width is `N` divided by `exp((log N)^{1/20})`: narrow enough that the comparison with the sharp
sum costs `o(N)`, wide enough that the price `((N+H+1)/H)² ≍ exp(2(log N)^{1/20})` is beaten by the
saving `exp(-c₀(log N)^{1/10}/8192)`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The smoothing ratio `N/H`. -/
noncomputable def smoothRatio (N : ℝ) : ℝ := Real.exp ((Real.log N) ^ ((1 : ℝ) / 20))

/-- The smoothing width. -/
noncomputable def smoothWidth (N : ℝ) : ℝ := N / smoothRatio N

theorem smoothRatio_pos (N : ℝ) : 0 < smoothRatio N := Real.exp_pos _

/-- The ratio is at least one once `log N ≥ 0`. -/
theorem one_le_smoothRatio {N : ℝ} (hN : 0 ≤ Real.log N) : 1 ≤ smoothRatio N := by
  rw [smoothRatio]
  exact Real.one_le_exp (by positivity)

/-- The width is at most the cutoff. -/
theorem smoothWidth_le {N : ℝ} (hN : 0 < N) (hlog : 0 ≤ Real.log N) : smoothWidth N ≤ N := by
  rw [smoothWidth, div_le_iff₀ (smoothRatio_pos N)]
  nlinarith [one_le_smoothRatio hlog, hN]

/-- The width is at least one once `log N ≥ 1`. -/
theorem one_le_smoothWidth {N : ℝ} (hN : 0 < N) (hlog : 1 ≤ Real.log N) :
    1 ≤ smoothWidth N := by
  have hexp : Real.exp ((Real.log N) ^ ((1 : ℝ) / 20)) ≤ N := by
    have hle : (Real.log N) ^ ((1 : ℝ) / 20) ≤ Real.log N := by
      calc (Real.log N) ^ ((1 : ℝ) / 20) ≤ (Real.log N) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
        _ = Real.log N := Real.rpow_one _
    calc Real.exp ((Real.log N) ^ ((1 : ℝ) / 20)) ≤ Real.exp (Real.log N) :=
          Real.exp_le_exp.2 hle
      _ = N := Real.exp_log hN
  rw [smoothWidth, le_div_iff₀ (smoothRatio_pos N), one_mul, smoothRatio]
  exact hexp

/-- The ratio recovered from the width. -/
theorem div_smoothWidth {N : ℝ} (hN : 0 < N) : N / smoothWidth N = smoothRatio N := by
  have hr : smoothRatio N ≠ 0 := ne_of_gt (smoothRatio_pos N)
  rw [smoothWidth]
  field_simp

/-- **The ratio tends to infinity.** -/
theorem tendsto_smoothRatio_atTop : Tendsto smoothRatio atTop atTop := by
  have h : Tendsto (fun N : ℝ => (Real.log N) ^ ((1 : ℝ) / 20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  exact Real.tendsto_exp_atTop.comp h

/-- **The comparison error is `o(N)`.** -/
theorem tendsto_smoothWidth_div : Tendsto (fun N : ℝ => (smoothWidth N + 1) / N) atTop (𝓝 0) := by
  have hinvratio : Tendsto (fun N : ℝ => (smoothRatio N)⁻¹) atTop (𝓝 0) :=
    tendsto_smoothRatio_atTop.inv_tendsto_atTop
  have hinvN : Tendsto (fun N : ℝ => N⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hsum : Tendsto (fun N : ℝ => (smoothRatio N)⁻¹ + N⁻¹) atTop (𝓝 (0 + 0)) :=
    hinvratio.add hinvN
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [smoothWidth]
  field_simp

end RHTower.Sieve
