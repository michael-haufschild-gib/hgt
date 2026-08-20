import GaloisForLFunctions.RHTower.SmoothAFEZetaMellin
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# Horizontal decay of the smooth-AFE integrand at a general point

The corpus discharges the horizontal Gaussian edges of the smooth approximate functional equation
only on the critical line.  Levinson's method needs the same identity at the abscissa
`σ₀ = ½ − R/log T`, so the decay has to hold at a general `s`.

Nothing about the critical line is used: the Gaussian kernel contributes `exp(u² − v²)/‖w‖`, the
power `x^w` contributes at most `max(x, x⁻¹)`, and `ζ` on the shifted strip is polynomially bounded
by the corpus's uniform strip estimate.  The product therefore tends to `0` for every fixed `s`,
along both horizontal edges.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

theorem norm_smoothAFEGaussianKernel_le_of_im {u v : ℝ} (hv : 0 < |v|)
    (huLow : -1 ≤ u) (huHigh : u ≤ 1) :
    ‖smoothAFEGaussianKernel ((u : ℂ) + (v : ℂ) * I)‖
      ≤ Real.exp 1 * Real.exp (-(v ^ 2)) / |v| := by
  set w : ℂ := (u : ℂ) + (v : ℂ) * I with hw
  have hre : (w ^ 2).re = u ^ 2 - v ^ 2 := by
    rw [hw, pow_two]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hwim : w.im = v := by rw [hw]; simp
  have hwnorm : |v| ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    rw [hwim] at h
    exact h
  have hexp : ‖Complex.exp (w ^ 2)‖ = Real.exp (u ^ 2 - v ^ 2) := by
    rw [Complex.norm_exp, hre]
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  have hnum : Real.exp (u ^ 2 - v ^ 2) ≤ Real.exp 1 * Real.exp (-(v ^ 2)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [smoothAFEGaussianKernel, norm_div, hexp]
  exact div_le_div₀ (by positivity) hnum hv hwnorm

/-- The pointwise horizontal majorant at a general base point. -/
theorem norm_smoothAFEZetaMellinIntegrand_general_le
    {x : ℝ} (hx : 0 < x) (s : ℂ) {C : ℝ} (hC0 : 0 ≤ C) {N : ℕ}
    (hC : ∀ σ t : ℝ, |σ| ≤ |s.re| + 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N)
    {u v : ℝ} (huLow : -1 ≤ u) (huHigh : u ≤ 1) (hv : |s.im| + 1 ≤ |v|) :
    ‖smoothAFEZetaMellinIntegrand s x ((u : ℂ) + (v : ℂ) * I)‖
      ≤ (C * max x x⁻¹ * Real.exp 1) * ((|s.im| + |v|) ^ N * Real.exp (-(v ^ 2))) := by
  set w : ℂ := (u : ℂ) + (v : ℂ) * I with hw
  have hsim0 : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hv1 : (1 : ℝ) ≤ |v| := by linarith
  have hvpos : (0 : ℝ) < |v| := by linarith
  have hwre : w.re = u := by rw [hw]; simp
  have hwim : w.im = v := by rw [hw]; simp
  have hsre : (s + w).re = s.re + u := by rw [Complex.add_re, hwre]
  have hsim : (s + w).im = s.im + v := by rw [Complex.add_im, hwim]
  have hzeta : ‖riemannZeta (s + w)‖ ≤ C * (|s.im| + |v|) ^ N := by
    have hrec : ((((s + w).re : ℝ)) : ℂ) + (((s + w).im : ℝ) : ℂ) * I = s + w :=
      Complex.re_add_im _
    have hreabs : |(s + w).re| ≤ |s.re| + 1 := by
      rw [hsre]
      have h1 : |s.re + u| ≤ |s.re| + |u| := abs_add_le _ _
      have h2 : |u| ≤ 1 := abs_le.mpr ⟨huLow, huHigh⟩
      linarith
    have himabs : |(s + w).im| ≤ |s.im| + |v| := by
      rw [hsim]
      exact abs_add_le _ _
    have himge : (1 : ℝ) ≤ |(s + w).im| := by
      rw [hsim]
      have h1 : |v| - |s.im| ≤ |s.im + v| := by
        have h := abs_sub_abs_le_abs_sub v (-s.im)
        simp only [abs_neg, sub_neg_eq_add] at h
        rw [add_comm v s.im] at h
        linarith [h]
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
  have hker := norm_smoothAFEGaussianKernel_le_of_im hvpos huLow huHigh
  have hkerT : ‖smoothAFEGaussianKernel w‖ ≤ Real.exp 1 * Real.exp (-(v ^ 2)) := by
    refine le_trans hker ?_
    rw [div_le_iff₀ hvpos]
    calc Real.exp 1 * Real.exp (-(v ^ 2))
        = Real.exp 1 * Real.exp (-(v ^ 2)) * 1 := by ring
      _ ≤ Real.exp 1 * Real.exp (-(v ^ 2)) * |v| :=
          mul_le_mul_of_nonneg_left hv1 (by positivity)
  rw [smoothAFEZetaMellinIntegrand, norm_mul, norm_mul]
  have hnn2 : (0 : ℝ) ≤ ‖(x : ℂ) ^ w‖ := norm_nonneg _
  have hCpow : (0 : ℝ) ≤ C * (|s.im| + |v|) ^ N := by positivity
  have hCmax : (0 : ℝ) ≤ C * (|s.im| + |v|) ^ N * max x x⁻¹ :=
    mul_nonneg hCpow (le_trans hnn2 hpow)
  calc ‖riemannZeta (s + w)‖ * ‖(x : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖
      ≤ (C * (|s.im| + |v|) ^ N) * (max x x⁻¹) * (Real.exp 1 * Real.exp (-(v ^ 2))) :=
        mul_le_mul (mul_le_mul hzeta hpow hnn2 hCpow) hkerT (norm_nonneg _) hCmax
    _ = (C * max x x⁻¹ * Real.exp 1) * ((|s.im| + |v|) ^ N * Real.exp (-(v ^ 2))) := by ring

theorem tendsto_shifted_pow_mul_exp_neg_sq (a : ℝ) (N : ℕ) :
    Tendsto (fun T : ℝ => (a + T) ^ N * Real.exp (-(T ^ 2))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun T : ℝ => T ^ N * Real.exp (-T)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hkey : Tendsto (fun T : ℝ => (2 ^ N * (|a| + 1) ^ N) * (T ^ N * Real.exp (-T)))
      atTop (𝓝 0) := by
    simpa using hbase.const_mul (2 ^ N * (|a| + 1) ^ N)
  refine squeeze_zero' ?_ ?_ hkey
  · filter_upwards [eventually_ge_atTop (|a| + 1)] with T hT
    have hnn : (0 : ℝ) ≤ a + T := by
      have h1 : -|a| ≤ a := neg_abs_le a
      have h2 : (0 : ℝ) ≤ |a| := abs_nonneg a
      linarith
    positivity
  · filter_upwards [eventually_ge_atTop (|a| + 1)] with T hT
    have h2 : (0 : ℝ) ≤ |a| := abs_nonneg a
    have hT1 : (1 : ℝ) ≤ T := by linarith
    have habs : a ≤ |a| := le_abs_self a
    have hsum : a + T ≤ 2 * T := by linarith
    have hnn : (0 : ℝ) ≤ a + T := by
      have h1 : -|a| ≤ a := neg_abs_le a
      linarith
    have hpow : (a + T) ^ N ≤ (2 * T) ^ N := pow_le_pow_left₀ hnn hsum N
    have hexp : Real.exp (-(T ^ 2)) ≤ Real.exp (-T) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    calc (a + T) ^ N * Real.exp (-(T ^ 2))
        ≤ (2 * T) ^ N * Real.exp (-T) :=
          mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
      _ = (2 : ℝ) ^ N * (T ^ N * Real.exp (-T)) := by rw [mul_pow]; ring
      _ ≤ (2 ^ N * (|a| + 1) ^ N) * (T ^ N * Real.exp (-T)) := by
          have h1 : (1 : ℝ) ≤ (|a| + 1) ^ N := one_le_pow₀ (by linarith)
          have h2' : (0 : ℝ) ≤ T ^ N * Real.exp (-T) := by positivity
          have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
          have h4 : (2 : ℝ) ^ N * 1 ≤ 2 ^ N * (|a| + 1) ^ N :=
            mul_le_mul_of_nonneg_left h1 h3
          calc (2 : ℝ) ^ N * (T ^ N * Real.exp (-T))
              = ((2 : ℝ) ^ N * 1) * (T ^ N * Real.exp (-T)) := by ring
            _ ≤ (2 ^ N * (|a| + 1) ^ N) * (T ^ N * Real.exp (-T)) :=
                mul_le_mul_of_nonneg_right h4 h2'

/-- **The horizontal Gaussian edges vanish at a general base point.**  `ε = 1` is the top edge and
`ε = -1` the bottom edge. -/
theorem tendsto_smoothAFEZetaMellinIntegrand_horizontal_general
    {x : ℝ} (hx : 0 < x) (s : ℂ) {ε : ℝ} (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-1)..1,
        smoothAFEZetaMellinIntegrand s x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_riemannZeta_strip (|s.re| + 1)
  set K : ℝ := C * max x x⁻¹ * Real.exp 1 with hK
  have hK0 : (0 : ℝ) ≤ K := by
    have hmax : (0 : ℝ) ≤ max x x⁻¹ := le_trans hx.le (le_max_left _ _)
    have := Real.exp_pos (1 : ℝ)
    positivity
  have hlim : Tendsto (fun T : ℝ => 2 * (K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2)))))
      atTop (𝓝 0) := by
    have h := (tendsto_shifted_pow_mul_exp_neg_sq |s.im| N).const_mul K
    simpa using h.const_mul (2 : ℝ)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (|s.im| + 1)] with T hT
  have hsim0 : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hT0 : (0 : ℝ) < T := by linarith
  have habsv : |ε * T| = T := by
    rw [abs_mul, hε, one_mul, abs_of_pos hT0]
  have hpoint : ∀ u ∈ Set.uIoc (-1 : ℝ) 1,
      ‖smoothAFEZetaMellinIntegrand s x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
    have hbound := norm_smoothAFEZetaMellinIntegrand_general_le hx s hC0 hC
      (u := u) (v := ε * T) hu.1.le hu.2 (by rw [habsv]; linarith)
    rw [habsv] at hbound
    have hsq : (ε * T) ^ 2 = T ^ 2 := by
      have : (ε * T) ^ 2 = ε ^ 2 * T ^ 2 := by ring
      rw [this, show ε ^ 2 = |ε| ^ 2 by rw [sq_abs], hε]
      ring
    rw [hsq] at hbound
    exact hbound
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have habs : |(1 : ℝ) - (-1)| = 2 := by norm_num
  rw [habs] at h
  calc ‖∫ u : ℝ in (-1 : ℝ)..1,
        smoothAFEZetaMellinIntegrand s x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) * 2 := h
    _ = 2 * (K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2)))) := by ring

end RHTower

end
