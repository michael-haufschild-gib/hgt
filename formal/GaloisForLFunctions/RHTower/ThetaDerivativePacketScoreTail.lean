import GaloisForLFunctions.RHTower.ThetaDerivativePacketLogConcavity

/-!
# Positive score tails of actual theta derivative packets

For every positive `m`, the score perturbation
`(1 - 303x²) k^{(4m)} - 16x k^{(4m+1)}` is continuous and eventually strictly positive.
The source ratio calculus gives the exact logarithmic-slope limit
`k^{(4m+1)}/k^{(4m)} + 2π exp(2x) → 8m + 9/2`.
Its exponential term dominates the linear slope threshold needed by the score operator.
No sign or spectral premise is imposed on the source.
-/

open Filter Topology Polynomial

namespace RHTower

noncomputable section

private theorem tendsto_thetaSourceRatio_one_add_twice_scale :
    Tendsto (fun x => thetaSourceRatio 1 x + 2 * thetaCuspSingleAtomReflectionScale 1 x)
      atTop (𝓝 (9 / 2 : ℝ)) := by
  have hdeg : thetaCuspSeedPolynomial.natDegree = 4 := by
    rw [show thetaCuspSeedPolynomial = thetaCuspLogDerivativePolynomial 0 from rfl,
      natDegree_thetaCuspLogDerivativePolynomial]
  have h0 := tendsto_polyLogSlope thetaCuspSeedPolynomial (by rw [hdeg]; norm_num)
  rw [hdeg] at h0
  have hmodel : Tendsto (fun x => (1 / 2 : ℝ) + polyLogSlope thetaCuspSeedPolynomial x)
      atTop (𝓝 (9 / 2 : ℝ)) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
      atTop (𝓝 (1 / 2 : ℝ))).add h0 using 1
    norm_num
  have hmodel' : Tendsto
      (fun x => thetaAtomRatio 1 x + 2 * thetaCuspSingleAtomReflectionScale 1 x)
      atTop (𝓝 (9 / 2 : ℝ)) := by
    apply Filter.Tendsto.congr' _ hmodel
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have ha := thetaAtomRatio_succ_div 0 hx (eval_thetaCuspSeedPolynomial_pos hx).ne'
    rw [thetaAtomRatio_zero hx, div_one,
      show thetaCuspLogDerivativePolynomial 0 = thetaCuspSeedPolynomial from rfl] at ha
    linarith
  have hclose : Tendsto (fun x => thetaSourceRatio 1 x - thetaAtomRatio 1 x)
      atTop (𝓝 (0 : ℝ)) :=
    ThetaTailNegligible.tendsto (thetaSourceRatio_close 1)
  convert hclose.add hmodel' using 1
  · funext x
    ring
  · norm_num

private theorem tendsto_thetaSourceRatio_four_mul_slope_add_twice_scale
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun x => thetaSourceRatio (4 * m + 1) x / thetaSourceRatio (4 * m) x +
        2 * thetaCuspSingleAtomReflectionScale 1 x)
      atTop (𝓝 (2 * ((4 * m : ℕ) : ℝ) + 9 / 2)) := by
  convert (tendsto_thetaSourceRatio_logSlope m hm).add
    tendsto_thetaSourceRatio_one_add_twice_scale using 1
  funext x
  ring

private theorem eventually_two_pi_exp_ge_affine (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, (303 / 16 : ℝ) * x + C ≤ 2 * Real.pi * Real.exp (2 * x) := by
  have hgrowth : Tendsto
      (fun x : ℝ => (2 * Real.pi * Real.exp (2 * x) - C) / (2 * x))
      atTop atTop := by
    simpa [Function.comp_def, pow_one, sub_eq_add_neg] using
      (Real.tendsto_mul_exp_add_div_pow_atTop (2 * Real.pi) (-C) 1
        (by positivity)).comp (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
  filter_upwards [hgrowth.eventually_ge_atTop (303 / 32 : ℝ),
    eventually_gt_atTop (0 : ℝ)] with x hg hx
  have h := (le_div_iff₀ (show 0 < 2 * x by positivity)).mp hg
  nlinarith

private theorem eventually_thetaSourceRatio_four_mul_slope_le (m : ℕ) (hm : 0 < m) :
    ∀ᶠ x : ℝ in atTop,
      thetaSourceRatio (4 * m + 1) x / thetaSourceRatio (4 * m) x ≤
        -(303 / 16 : ℝ) * x - 1 := by
  have hlim := tendsto_thetaSourceRatio_four_mul_slope_add_twice_scale m hm
  filter_upwards [hlim.eventually_lt_const
      (show 2 * ((4 * m : ℕ) : ℝ) + 9 / 2 <
        2 * ((4 * m : ℕ) : ℝ) + 11 / 2 by linarith),
    eventually_two_pi_exp_ge_affine (2 * ((4 * m : ℕ) : ℝ) + 13 / 2)] with x hs hg
  have hscale : thetaCuspSingleAtomReflectionScale 1 x = Real.pi * Real.exp (2 * x) := by
    simp [thetaCuspSingleAtomReflectionScale]
  rw [hscale] at hs
  linarith

private theorem eventually_iteratedDeriv_four_mul_thetaCuspFullSource_pos
    (m : ℕ) (hm : 0 < m) :
    ∀ᶠ x : ℝ in atTop, 0 < iteratedDeriv (4 * m) thetaCuspFullSource x := by
  filter_upwards [eventually_half_le_thetaSourceRatio m hm] with x hx
  have hratio : 0 < thetaSourceRatio (4 * m) x := by linarith
  exact ((div_pos_iff.mp hratio).resolve_right
    (not_and.mpr fun _ => not_lt.mpr (thetaCuspFullSource_pos_all x).le)).1

/-- The literal score perturbation of every theta derivative packet is continuous on `ℝ`. -/
theorem continuous_thetaDerivativePacketScorePerturbation (m : ℕ) :
    Continuous (fun x : ℝ =>
      (1 - 303 * x ^ 2) * iteratedDeriv (4 * m) thetaCuspFullSource x -
        16 * x * iteratedDeriv (4 * m + 1) thetaCuspFullSource x) := by
  exact ((continuous_const.sub (continuous_const.mul (continuous_id.pow 2))).mul
    (continuous_iteratedDeriv_thetaCuspFullSource (4 * m))).sub
    ((continuous_const.mul continuous_id).mul
      (continuous_iteratedDeriv_thetaCuspFullSource (4 * m + 1)))

/-- The actual `4m`th theta derivative has a strictly positive score on the positive tail. -/
theorem eventually_thetaDerivativePacketScorePerturbation_pos (m : ℕ) (hm : 0 < m) :
    ∀ᶠ x : ℝ in atTop,
      0 < (1 - 303 * x ^ 2) * iteratedDeriv (4 * m) thetaCuspFullSource x -
        16 * x * iteratedDeriv (4 * m + 1) thetaCuspFullSource x := by
  filter_upwards [eventually_iteratedDeriv_four_mul_thetaCuspFullSource_pos m hm,
    eventually_thetaSourceRatio_four_mul_slope_le m hm,
    eventually_ge_atTop (0 : ℝ)] with x hh hs hx
  have hsource := (thetaCuspFullSource_pos_all x).ne'
  have heq :
      thetaSourceRatio (4 * m + 1) x / thetaSourceRatio (4 * m) x =
        iteratedDeriv (4 * m + 1) thetaCuspFullSource x /
          iteratedDeriv (4 * m) thetaCuspFullSource x := by
    unfold thetaSourceRatio
    field_simp
  rw [heq, div_le_iff₀ hh] at hs
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 16 * x by positivity)
  have hpos : 0 < (1 + 16 * x) * iteratedDeriv (4 * m) thetaCuspFullSource x := by
    positivity
  nlinarith

end

end RHTower
