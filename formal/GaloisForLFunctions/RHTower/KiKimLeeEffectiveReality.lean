import GaloisForLFunctions.RHTower.KiKimLeeUniformReality

/-!
# Ki–Kim–Lee reality with an explicit height

For `0 < t ≤ 1/8`, every zero of the de Bruijn–Newman deformation `H_t` with
`|Re z| ≥ 2π e^{40/t}` is real (`riemannHeat_zeros_real_of_le_re`). Hence all nonreal zeros of `H_t`
lie in the box `|Re z| < 2π e^{40/t}`, `|Im z| ≤ ½`.

The Ki–Kim–Lee comparison at height `X` has slope `α = ½ log(X/2π)`. Its relative error is bounded
by `kklErrorUniform t α`, a sum of five terms, and each term is `≤ e^{−α}` once `tα ≥ 20`
(`kklErrorUniform_le_of_mul_ge`). The five terms are
`e^{5α/2 − 3tα²/4}`, `e^{−α² + 5/8}`, a Gaussian tail `≍ t^{−1/2}(1/t + α)e^{7α − tα²}`,
a Stirling term `≍ (1/t + α)e^{−7α²/4 + α}`, and a quartic term `≍ t^{−1/2}e^{−2α⁴ + α³}`.
The height `X = 2π e^{40/t}` is `α = 20/t`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- `x^{−1/2} ≤ 1 + 1/x` for `x > 0`. -/
theorem rpow_neg_half_le_one_add_inv {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2 : ℝ)) ≤ 1 + x⁻¹ := by
  rcases le_or_gt 1 x with h1 | h1
  · have : x ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
    have : 0 ≤ x⁻¹ := by positivity
    linarith
  · have h2 : x ^ (-(1 / 2 : ℝ)) ≤ x ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx h1.le (by norm_num)
    rw [Real.rpow_neg_one] at h2
    linarith

/-- **The explicit Ki–Kim–Lee error.** If `0 < t ≤ 1/8` and `tα ≥ 20`, then
`kklErrorUniform t α ≤ 1/8`. -/
theorem kklErrorUniform_le_of_mul_ge {t α : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (htα : 20 ≤ t * α) : kklErrorUniform t α ≤ 1 / 8 := by
  have hα160 : 160 ≤ α := by
    by_contra h; push Not at h
    have : t * α ≤ 1 / 8 * α := mul_le_mul_of_nonneg_right ht8 (by nlinarith)
    nlinarith
  have hα0 : 0 < α := by linarith
  set E := Real.exp (-α) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- auxiliary bounds
  have hinvt : 1 / t ≤ α / 20 := by rw [div_le_div_iff₀ ht (by norm_num)]; linarith
  have hr : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) ≤ Real.exp α := by
    refine (rpow_neg_half_le_one_add_inv (by positivity)).trans ?_
    have h1 : (4 * Real.pi * t)⁻¹ ≤ α := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      have := Real.pi_gt_three
      have e : α * (4 * Real.pi * t) = 4 * Real.pi * (t * α) := by ring
      rw [e]
      nlinarith
    have := Real.add_one_le_exp α
    linarith
  have hr0 : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by positivity
  -- term 1
  have h1 : Real.exp (5 / 2 * α - 3 / 4 * t * α ^ 2) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have : 3 / 4 * t * α ^ 2 = 3 / 4 * (t * α) * α := by ring
    rw [this]; nlinarith
  -- term 2
  have h2 : Real.exp (-α ^ 2 + 1 / 2 + 1 / 8) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr; nlinarith
  -- term 3
  have h3 : 2 * (9 / 2 * (5 / (2 * t) + α + 1) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 200 *
      (6 + 2 * Real.pi * Real.exp (2 * α)) *
      Real.exp (5 * α - t * α ^ 2 + (1 / 2 + α / 4) / 8)) ≤ E := by
    have ha : 5 / (2 * t) + α + 1 ≤ Real.exp (α / 8 + α) := by
      have := Real.add_one_le_exp (5 / (2 * t) + α)
      have h5 : 5 / (2 * t) ≤ α / 8 := by
        have : 5 / (2 * t) = 5 / 2 * (1 / t) := by ring
        rw [this]; linarith
      exact this.trans (Real.exp_le_exp.mpr (by linarith))
    have hb : 6 + 2 * Real.pi * Real.exp (2 * α) ≤ 13 * Real.exp (2 * α) := by
      have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * α)
      have := Real.pi_lt_d2
      nlinarith
    have hc : Real.exp (5 * α - t * α ^ 2 + (1 / 2 + α / 4) / 8) ≤
        Real.exp (-15 * α + α / 32 + 1 / 16) := by
      apply Real.exp_le_exp.mpr
      have : t * α ^ 2 = (t * α) * α := by ring
      rw [this]; nlinarith
    have hprod : 2 * (9 / 2 * (5 / (2 * t) + α + 1) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 200 *
        (6 + 2 * Real.pi * Real.exp (2 * α)) *
        Real.exp (5 * α - t * α ^ 2 + (1 / 2 + α / 4) / 8)) ≤
        23400 * (Real.exp (α / 8 + α) * Real.exp α * Real.exp (2 * α) *
          Real.exp (-15 * α + α / 32 + 1 / 16)) := by
      have hp1 : 0 ≤ 5 / (2 * t) + α + 1 := by positivity
      calc 2 * (9 / 2 * (5 / (2 * t) + α + 1) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 200 *
            (6 + 2 * Real.pi * Real.exp (2 * α)) *
            Real.exp (5 * α - t * α ^ 2 + (1 / 2 + α / 4) / 8))
          = 1800 * ((5 / (2 * t) + α + 1) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
            (6 + 2 * Real.pi * Real.exp (2 * α)) *
            Real.exp (5 * α - t * α ^ 2 + (1 / 2 + α / 4) / 8)) := by ring
        _ ≤ 1800 * (Real.exp (α / 8 + α) * Real.exp α * (13 * Real.exp (2 * α)) *
            Real.exp (-15 * α + α / 32 + 1 / 16)) := by gcongr
        _ = 23400 * (Real.exp (α / 8 + α) * Real.exp α * Real.exp (2 * α) *
            Real.exp (-15 * α + α / 32 + 1 / 16)) := by ring
    refine hprod.trans ?_
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    have hK : (23400 : ℝ) ≤ Real.exp (9 * α) := by
      have := Real.pow_div_factorial_le_exp (9 * α) (by positivity) 2
      norm_num [Nat.factorial] at this
      nlinarith
    calc 23400 * Real.exp (α / 8 + α + α + 2 * α + (-15 * α + α / 32 + 1 / 16))
        ≤ Real.exp (9 * α) * Real.exp (α / 8 + α + α + 2 * α + (-15 * α + α / 32 + 1 / 16)) :=
          mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
      _ = Real.exp (9 * α + (α / 8 + α + α + 2 * α + (-15 * α + α / 32 + 1 / 16))) :=
          (Real.exp_add _ _).symm
      _ ≤ E := by rw [hE]; apply Real.exp_le_exp.mpr; nlinarith
  -- term 4
  have h4 : 2 * (2 * Real.exp 1 * 2 * (1 / (2 * t) + α + 1) *
      Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8)) ≤ E := by
    have ha : 1 / (2 * t) + α + 1 ≤ Real.exp (α / 40 + α) := by
      have := Real.add_one_le_exp (1 / (2 * t) + α)
      have h5 : 1 / (2 * t) ≤ α / 40 := by
        have : 1 / (2 * t) = 1 / 2 * (1 / t) := by ring
        rw [this]; linarith
      exact this.trans (Real.exp_le_exp.mpr (by linarith))
    have he1 : Real.exp 1 ≤ Real.exp α := Real.exp_le_exp.mpr (by linarith)
    calc 2 * (2 * Real.exp 1 * 2 * (1 / (2 * t) + α + 1) *
          Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8))
        ≤ 8 * (Real.exp α * Real.exp (α / 40 + α) *
          Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8)) := by
          have hp1 : 0 ≤ 1 / (2 * t) + α + 1 := by positivity
          calc 2 * (2 * Real.exp 1 * 2 * (1 / (2 * t) + α + 1) *
                Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8))
              = 8 * (Real.exp 1 * (1 / (2 * t) + α + 1) *
                Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8)) := by ring
            _ ≤ 8 * (Real.exp α * Real.exp (α / 40 + α) *
                Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8)) := by gcongr
      _ = 8 * Real.exp (α + (α / 40 + α) + (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α +
            18 / 8)) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp α * Real.exp (α + (α / 40 + α) + (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α +
            18 / 8)) := by
          have : (8 : ℝ) ≤ Real.exp α := by
            have := Real.add_one_le_exp α; linarith
          exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = Real.exp (α + (α + (α / 40 + α) + (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α +
            18 / 8))) := (Real.exp_add _ _).symm
      _ ≤ E := by rw [hE]; apply Real.exp_le_exp.mpr; nlinarith
  -- term 5
  have h5 : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(2 * (α ^ 2 - 1 / 2) ^ 2) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + α ^ 2 / 8) ≤ E := by
    have hq : -(2 * (α ^ 2 - 1 / 2) ^ 2) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + α ^ 2 / 8 ≤
        -α ^ 2 := by
      have hexp : (α ^ 2 - 1 / 2) ^ 2 = α ^ 4 - α ^ 2 + 1 / 4 := by ring
      have hprod : (α ^ 2 + 1 / 2) * (α + 1 / 8) = α ^ 3 + α ^ 2 / 8 + α / 2 + 1 / 16 := by ring
      rw [hexp, hprod]
      have ha1 : 3 * α ≤ α ^ 2 := by nlinarith
      have ha2 : 3 * α ^ 2 ≤ α ^ 3 := by nlinarith
      have ha3 : 3 * α ^ 3 ≤ α ^ 4 := by nlinarith
      nlinarith
    calc (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 * (α ^ 2 - 1 / 2) ^ 2) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + α ^ 2 / 8)
        ≤ Real.exp α * Real.exp (-α ^ 2) :=
          mul_le_mul hr (Real.exp_le_exp.mpr hq) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (α + -α ^ 2) := (Real.exp_add _ _).symm
      _ ≤ E := by rw [hE]; apply Real.exp_le_exp.mpr; nlinarith
  -- the sum
  have hE8 : 7 * E ≤ 1 / 8 := by
    rw [hE, Real.exp_neg]
    have := Real.add_one_le_exp α
    rw [mul_inv_le_iff₀ (Real.exp_pos _)]
    linarith
  unfold kklErrorUniform
  linarith

/-- **Explicit large-height nonvanishing.** For `0 < t ≤ 1/8` and `X ≥ 2π e^{40/t}`,
`H_t(X + iy) ≠ 0` for `0 < |y| ≤ ½`. -/
theorem riemannHeat_ne_zero_of_le {t X : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 2 * Real.pi * Real.exp (40 / t) ≤ X) {y : ℝ} (hy0 : y ≠ 0) (hy : |y| ≤ 1 / 2) :
    riemannHeat t ((X : ℂ) + I * y) ≠ 0 := by
  have h2π : 0 < 2 * Real.pi := by positivity
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  set α := (horizontalSlope X).re with hαdef
  have hα : 20 / t ≤ α := by
    rw [hαdef, horizontalSlope_re]
    have h1 : Real.exp (40 / t) ≤ X / (2 * Real.pi) := by rw [le_div_iff₀ h2π]; linarith
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    have : 40 / t / 2 = 20 / t := by ring
    linarith
  have htα : 20 ≤ t * α := by
    have := mul_le_mul_of_nonneg_left hα ht.le
    rw [mul_div_cancel₀ _ ht.ne'] at this
    exact this
  have hinvt : 8 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
  have hα160 : 160 ≤ α := by
    have : 20 * 8 ≤ 20 / t := by
      rw [show 20 / t = 20 * (1 / t) by ring]; linarith
    linarith
  have hX200 : 200 ≤ X := by
    have h1 : (1 : ℝ) + 320 ≤ Real.exp (40 / t) := by
      have := Real.add_one_le_exp (40 / t)
      have : 320 ≤ 40 / t := by rw [show 40 / t = 40 * (1 / t) by ring]; linarith
      linarith
    have := Real.pi_gt_three
    nlinarith
  refine riemannHeat_ne_zero_of_re_slope_pos ht (fun v hv => ?_) hy0 hy
  refine re_slope_mul_conj_pos ht ht8 hX200 hv (by linarith) ?_
    (window_fits ht8 ht hX0 (by linarith))
    ((kklError_le_uniform ht le_rfl ht8 (by linarith)).trans
      (kklErrorUniform_le_of_mul_ge ht ht8 htα))
  have := mul_le_mul_of_nonneg_left hα (by positivity : (0 : ℝ) ≤ 2 * t)
  rw [show 2 * t * (20 / t) = 40 by field_simp; ring] at this
  linarith

/-- **Ki–Kim–Lee reality with an explicit height.** For `0 < t ≤ 1/8`, every zero of `H_t` with
`|Re z| ≥ 2π e^{40/t}` is real. -/
theorem riemannHeat_zeros_real_of_le_re {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) {z : ℂ}
    (hz : riemannHeat t z = 0) (hre : 2 * Real.pi * Real.exp (40 / t) ≤ |z.re|) : z.im = 0 := by
  have him := riemannHeat_zeros_im_sq_le ht hz
  have him2 : z.im ^ 2 ≤ 1 / 4 := him.trans (max_le (by linarith) (by norm_num))
  have him' : |z.im| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  by_contra hne
  rcases le_or_gt 0 z.re with h0 | h0
  · rw [abs_of_nonneg h0] at hre
    apply riemannHeat_ne_zero_of_le ht ht8 hre hne him'
    rw [← hz]
    congr 1
    apply Complex.ext <;> simp
  · rw [abs_of_neg h0] at hre
    apply riemannHeat_ne_zero_of_le ht ht8 (X := (-z).re) (by simpa using hre)
      (y := (-z).im) (by simpa using hne) (by simpa using him')
    rw [← hz, ← riemannHeat_neg ht.le]
    congr 1
    apply Complex.ext <;> simp

end

end RHTower.DeBruijn
