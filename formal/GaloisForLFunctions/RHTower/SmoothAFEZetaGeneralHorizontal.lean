import GaloisForLFunctions.RHTower.SmoothAFEZetaMellin

/-!
# Horizontal decay of the smooth-AFE integrand at a general point

The corpus discharges the horizontal Gaussian edges of the smooth approximate functional equation
only on the critical line.  Levinson's method needs the same identity at the abscissa
`σ₀ = ½ − R/log T`, so the decay has to hold at a general `s`.

Nothing about the critical line is used: the Gaussian kernel contributes `exp(u² − T²)/‖w‖`, the
power `x^w` contributes at most `max(x, x⁻¹)`, and `ζ` on the shifted strip is polynomially bounded
by the corpus's uniform strip estimate.  The product therefore tends to `0` for every fixed `s`.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

theorem norm_smoothAFEGaussianKernel_le_of_im {u T : ℝ} (hT : 0 < T)
    (huLow : -1 ≤ u) (huHigh : u ≤ 1) :
    ‖smoothAFEGaussianKernel ((u : ℂ) + (T : ℂ) * I)‖
      ≤ Real.exp 1 * Real.exp (-(T ^ 2)) / T := by
  set w : ℂ := (u : ℂ) + (T : ℂ) * I with hw
  have hre : (w ^ 2).re = u ^ 2 - T ^ 2 := by
    rw [hw, pow_two]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hwim : w.im = T := by rw [hw]; simp
  have hwnorm : T ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    rw [hwim, abs_of_pos hT] at h
    exact h
  have hwpos : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le hT hwnorm
  have hexp : ‖Complex.exp (w ^ 2)‖ = Real.exp (u ^ 2 - T ^ 2) := by
    rw [Complex.norm_exp, hre]
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  have hnum : Real.exp (u ^ 2 - T ^ 2) ≤ Real.exp 1 * Real.exp (-(T ^ 2)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [smoothAFEGaussianKernel, norm_div, hexp]
  refine div_le_div (by positivity) hnum hT hwnorm

theorem norm_smoothAFEZetaMellinIntegrand_general_le
    {x : ℝ} (hx : 0 < x) (s : ℂ) {C : ℝ} (hC0 : 0 ≤ C) {N : ℕ}
    (hC : ∀ σ t : ℝ, |σ| ≤ |s.re| + 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N)
    {u T : ℝ} (huLow : -1 ≤ u) (huHigh : u ≤ 1) (hT : |s.im| + 1 ≤ T) (hT1 : 1 ≤ T) :
    ‖smoothAFEZetaMellinIntegrand s x ((u : ℂ) + (T : ℂ) * I)‖
      ≤ (C * max x x⁻¹ * Real.exp 1) * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) := by
  set w : ℂ := (u : ℂ) + (T : ℂ) * I with hw
  have hT0 : (0 : ℝ) < T := by linarith
  have hwre : w.re = u := by rw [hw]; simp
  have hwim : w.im = T := by rw [hw]; simp
  have hsre : (s + w).re = s.re + u := by rw [Complex.add_re, hwre]
  have hsim : (s + w).im = s.im + T := by rw [Complex.add_im, hwim]
  have hzeta : ‖riemannZeta (s + w)‖ ≤ C * (|s.im| + T) ^ N := by
    have hrec : ((((s + w).re : ℝ)) : ℂ) + (((s + w).im : ℝ) : ℂ) * I = s + w :=
      Complex.re_add_im _
    have hreabs : |(s + w).re| ≤ |s.re| + 1 := by
      rw [hsre]
      have h1 : |s.re + u| ≤ |s.re| + |u| := abs_add_le _ _
      have h2 : |u| ≤ 1 := abs_le.mpr ⟨huLow, huHigh⟩
      linarith
    have himabs : |(s + w).im| ≤ |s.im| + T := by
      rw [hsim]
      have h1 : |s.im + T| ≤ |s.im| + |T| := abs_add_le _ _
      rw [abs_of_pos hT0] at h1
      exact h1
    have himge : (1 : ℝ) ≤ |(s + w).im| := by
      rw [hsim]
      have hnn : -|s.im| ≤ s.im := neg_abs_le _
      rw [le_abs]
      left
      linarith
    have hbase := hC (s + w).re (s + w).im hreabs himge
    rw [hrec] at hbase
    refine le_trans hbase ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) himabs N) hC0
  have hpow : ‖(x : ℂ) ^ w‖ ≤ max x x⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hwre]
    rcases le_total 1 x with h1 | h1
    · refine le_trans (Real.rpow_le_rpow_of_exponent_le h1 huHigh) ?_
      rw [Real.rpow_one]
      exact le_max_left _ _
    · have hinv : x ^ u ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx h1 huLow
      rw [Real.rpow_neg_one] at hinv
      exact le_trans hinv (le_max_right _ _)
  have hker := norm_smoothAFEGaussianKernel_le_of_im hT0 huLow huHigh
  have hkerT : ‖smoothAFEGaussianKernel w‖ ≤ Real.exp 1 * Real.exp (-(T ^ 2)) := by
    refine le_trans hker ?_
    rw [div_le_iff₀ hT0]
    nlinarith [Real.exp_pos (-(T ^ 2)), Real.exp_pos (1 : ℝ), hT1]
  rw [smoothAFEZetaMellinIntegrand, norm_mul, norm_mul]
  have hnn1 : (0 : ℝ) ≤ ‖riemannZeta (s + w)‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖(x : ℂ) ^ w‖ := norm_nonneg _
  calc ‖riemannZeta (s + w)‖ * ‖(x : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖
      ≤ (C * (|s.im| + T) ^ N) * (max x x⁻¹) * (Real.exp 1 * Real.exp (-(T ^ 2))) := by
        gcongr
        · exact le_trans hnn2 hpow
        · exact hzeta
    _ = (C * max x x⁻¹ * Real.exp 1) * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) := by ring

theorem tendsto_shifted_pow_mul_exp_neg_sq (a : ℝ) (N : ℕ) :
    Tendsto (fun T : ℝ => (a + T) ^ N * Real.exp (-(T ^ 2))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun T : ℝ => T ^ N * Real.exp (-T)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hkey : Tendsto (fun T : ℝ => (2 ^ N * (|a| + 1) ^ N) * (T ^ N * Real.exp (-T)))
      atTop (𝓝 0) := by
    simpa using hbase.const_mul (2 ^ N * (|a| + 1) ^ N)
  refine squeeze_zero' ?_ ?_ hkey
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    positivity
  · filter_upwards [eventually_ge_atTop (|a| + 1)] with T hT
    have hT1 : (1 : ℝ) ≤ T := le_trans (by positivity) hT
    have hT0 : (0 : ℝ) < T := by linarith
    have habs : a ≤ |a| := le_abs_self a
    have hsum : a + T ≤ 2 * T := by
      have : |a| ≤ T := by linarith
      linarith
    have hnn : (0 : ℝ) ≤ a + T := by
      have : -|a| ≤ a := neg_abs_le a
      linarith
    have hpow : (a + T) ^ N ≤ (2 * T) ^ N := pow_le_pow_left₀ hnn hsum N
    have hexp : Real.exp (-(T ^ 2)) ≤ Real.exp (-T) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    calc (a + T) ^ N * Real.exp (-(T ^ 2))
        ≤ (2 * T) ^ N * Real.exp (-T) := by
          exact mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
      _ = (2 ^ N) * (T ^ N * Real.exp (-T)) := by rw [mul_pow]; ring
      _ ≤ (2 ^ N * (|a| + 1) ^ N) * (T ^ N * Real.exp (-T)) := by
          have h1 : (1 : ℝ) ≤ (|a| + 1) ^ N := one_le_pow₀ (by positivity)
          have h2 : (0 : ℝ) ≤ T ^ N * Real.exp (-T) := by positivity
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) N]

end RHTower

end
