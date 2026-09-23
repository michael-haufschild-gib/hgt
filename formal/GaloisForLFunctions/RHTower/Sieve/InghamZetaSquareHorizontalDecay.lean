import GaloisForLFunctions.RHTower.Sieve.InghamLeftContourGammaDecay
import GaloisForLFunctions.RHTower.TitchmarshZetaInputs

/-!
# Horizontal decay for Ingham's zeta-square Mellin contour

Uniform arbitrary-power Gamma decay on `-3/4 <= Re z <= 2` beats coarse quartic growth of
`zeta(s+z)^(2 : ℕ)`.  This closes both horizontal-edge limits without Stirling asymptotics.
-/

noncomputable section

open Complex Set Filter Topology

namespace RHTower.Sieve

/-- Positive-base complex power is uniformly bounded on Ingham horizontal strip. -/
theorem norm_cpow_neg_ingham_horizontal_le
    {x u T : ℝ} (hx : 0 < x) (huLow : -3 / 4 ≤ u) (huHigh : u ≤ 2) :
    ‖(x : ℂ) ^ (-((u : ℂ) + (T : ℂ) * I))‖ ≤
      Real.exp (2 * |Real.log x|) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  calc
    Real.log x * -u ≤ |Real.log x * -u| := le_abs_self _
    _ = |Real.log x| * |u| := by rw [abs_mul, abs_neg]
    _ ≤ |Real.log x| * 2 := by
      gcongr
      rw [abs_le]
      constructor <;> linarith
    _ = 2 * |Real.log x| := by ring

/-- Coarse but uniform horizontal bound: zeta-square costs degree four and Gamma supplies six
inverse powers. -/
theorem exists_norm_inghamZetaSquareMellinIntegrand_horizontal_le
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u T : ℝ, -3 / 4 ≤ u → u ≤ 2 →
      1 ≤ |T| → 2 ≤ |tau + T| →
      ‖inghamZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
        C * (1 + |tau + T|) ^ 4 / |T| ^ 6 := by
  obtain ⟨G, hG, hGamma⟩ := exists_uniform_bound_norm_Gamma_ingham_strip 6
  let C : ℝ := Real.exp (2 * |Real.log x|) * G * (20 * Real.exp 4) ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u T huLow huHigh hT hheight
  have hxpow := norm_cpow_neg_ingham_horizontal_le hx huLow huHigh (T := T)
  have hgamma := hGamma u T huLow huHigh hT
  have hzeta :
      ‖riemannZeta (linePt tau + ((u : ℂ) + (T : ℂ) * I))‖ ≤
        20 * Real.exp 4 * (1 + |tau + T|) ^ 2 := by
    rw [RHTower.linePt_add_horizontal_eq]
    exact RHTower.norm_riemannZeta_le_titchmarsh_strip
      (by linarith) (by linarith) hheight
  rw [inghamZetaSquareMellinIntegrand, norm_mul, norm_mul, norm_pow]
  calc
    ‖(x : ℂ) ^ (-((u : ℂ) + (T : ℂ) * I))‖ *
          ‖Complex.Gamma ((u : ℂ) + (T : ℂ) * I)‖ *
          ‖riemannZeta (linePt tau + ((u : ℂ) + (T : ℂ) * I))‖ ^ 2
        ≤ Real.exp (2 * |Real.log x|) * (G / |T| ^ 6) *
            (20 * Real.exp 4 * (1 + |tau + T|) ^ 2) ^ 2 := by
      gcongr
    _ = C * (1 + |tau + T|) ^ 4 / |T| ^ 6 := by
      dsimp only [C]
      ring

/-- Top horizontal edge tends to zero. -/
theorem tendsto_inghamZetaSquareMellinIntegrand_horizontal_top
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-3 / 4)..2,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_inghamZetaSquareMellinIntegrand_horizontal_le hx tau
  let D : ℝ := (11 / 4 : ℝ) * C * (2 + |tau|) ^ 4
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hmajor : Tendsto (fun T : ℝ => D * (T ^ 4 / T ^ 6)) atTop (𝓝 0) := by
    have hratio : Tendsto (fun T : ℝ => T ^ 4 / T ^ 6) atTop (𝓝 0) :=
      tendsto_pow_div_pow_atTop_zero (by norm_num)
    have hconst : Tendsto (fun _T : ℝ => D) atTop (𝓝 D) := tendsto_const_nhds
    simpa using hconst.mul hratio
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|tau| + 2))] with T hTlarge
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hTlarge
  have hheight0 : |tau| + 2 ≤ T := le_trans (le_max_right _ _) hTlarge
  have hTabs : |T| = T := abs_of_nonneg (zero_le_one.trans hT1)
  have hheight : 2 ≤ |tau + T| := by
    have htri : |T| ≤ |tau + T| + |tau| := by
      have := abs_sub_le (tau + T) 0 tau
      simpa only [sub_zero, add_sub_cancel_left, zero_sub, abs_neg] using this
    rw [hTabs] at htri
    linarith
  have hheightUpper : |tau + T| ≤ |tau| + T := by
    calc
      |tau + T| ≤ |tau| + |T| := abs_add_le tau T
      _ = |tau| + T := by rw [hTabs]
  have hpoint : ∀ u ∈ uIoc (-3 / 4 : ℝ) 2,
      ‖inghamZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
        C * (1 + |tau| + T) ^ 4 / T ^ 6 := by
    intro u hu
    have hu' : -3 / 4 ≤ u ∧ u ≤ 2 := by
      rw [uIoc_of_le (by norm_num)] at hu
      exact ⟨hu.1.le, hu.2⟩
    have hb := hbound u T hu'.1 hu'.2 (by rw [hTabs]; exact hT1) hheight
    rw [hTabs] at hb
    exact hb.trans (by
      have hp : (1 + |tau + T|) ^ 4 ≤ (1 + |tau| + T) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp hC) (by positivity))
  have hintegral :
      ‖∫ u : ℝ in (-3 / 4)..2,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) + (T : ℂ) * I)‖ ≤
        (11 / 4 : ℝ) * (C * (1 + |tau| + T) ^ 4 / T ^ 6) := by
    calc
      ‖∫ u : ℝ in (-3 / 4)..2,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) + (T : ℂ) * I)‖ ≤
          (C * (1 + |tau| + T) ^ 4 / T ^ 6) * |(2 : ℝ) - (-3 / 4)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      _ = (11 / 4 : ℝ) * (C * (1 + |tau| + T) ^ 4 / T ^ 6) := by
        norm_num
        ring
  calc
    ‖∫ u : ℝ in (-3 / 4)..2,
        inghamZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
        (11 / 4 : ℝ) * (C * (1 + |tau| + T) ^ 4 / T ^ 6) := hintegral
    _ ≤ (11 / 4 : ℝ) * (C * (((2 + |tau|) * T) ^ 4) / T ^ 6) := by
      have hlinear : 1 + |tau| + T ≤ (2 + |tau|) * T := by
        nlinarith [abs_nonneg tau]
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |tau| + T) hlinear 4
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (by positivity))
        (by norm_num)
    _ = D * (T ^ 4 / T ^ 6) := by
      dsimp only [D]
      rw [mul_pow]
      ring

/-- Bottom horizontal edge tends to zero. -/
theorem tendsto_inghamZetaSquareMellinIntegrand_horizontal_bottom
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-3 / 4)..2,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_inghamZetaSquareMellinIntegrand_horizontal_le hx tau
  let D : ℝ := (11 / 4 : ℝ) * C * (2 + |tau|) ^ 4
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hmajor : Tendsto (fun T : ℝ => D * (T ^ 4 / T ^ 6)) atTop (𝓝 0) := by
    have hratio : Tendsto (fun T : ℝ => T ^ 4 / T ^ 6) atTop (𝓝 0) :=
      tendsto_pow_div_pow_atTop_zero (by norm_num)
    have hconst : Tendsto (fun _T : ℝ => D) atTop (𝓝 D) := tendsto_const_nhds
    simpa using hconst.mul hratio
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|tau| + 2))] with T hTlarge
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hTlarge
  have hheight0 : |tau| + 2 ≤ T := le_trans (le_max_right _ _) hTlarge
  have hTabs : |T| = T := abs_of_nonneg (zero_le_one.trans hT1)
  have hheight : 2 ≤ |tau - T| := by
    have htri : |T| ≤ |tau - T| + |tau| := by
      have := abs_sub_le tau 0 (tau - T)
      simpa only [sub_zero, zero_sub, abs_neg, sub_sub_cancel, add_comm] using this
    rw [hTabs] at htri
    linarith
  have hheightUpper : |tau - T| ≤ |tau| + T := by
    calc
      |tau - T| = |tau + (-T)| := by rw [sub_eq_add_neg]
      _ ≤ |tau| + |-T| := abs_add_le tau (-T)
      _ = |tau| + T := by rw [abs_neg, hTabs]
  have hpoint : ∀ u ∈ uIoc (-3 / 4 : ℝ) 2,
      ‖inghamZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) - (T : ℂ) * I)‖ ≤
        C * (1 + |tau| + T) ^ 4 / T ^ 6 := by
    intro u hu
    have hu' : -3 / 4 ≤ u ∧ u ≤ 2 := by
      rw [uIoc_of_le (by norm_num)] at hu
      exact ⟨hu.1.le, hu.2⟩
    have hb := hbound u (-T) hu'.1 hu'.2
      (by simpa [abs_neg, hTabs] using hT1)
      (by simpa only [sub_eq_add_neg] using hheight)
    have hb' :
        ‖inghamZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) - (T : ℂ) * I)‖ ≤
          C * (1 + |tau - T|) ^ 4 / T ^ 6 := by
      simpa [sub_eq_add_neg, ofReal_neg, abs_neg, hTabs] using hb
    exact hb'.trans (by
      have hp : (1 + |tau - T|) ^ 4 ≤ (1 + |tau| + T) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp hC) (by positivity))
  have hintegral :
      ‖∫ u : ℝ in (-3 / 4)..2,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) - (T : ℂ) * I)‖ ≤
        (11 / 4 : ℝ) * (C * (1 + |tau| + T) ^ 4 / T ^ 6) := by
    calc
      ‖∫ u : ℝ in (-3 / 4)..2,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) - (T : ℂ) * I)‖ ≤
          (C * (1 + |tau| + T) ^ 4 / T ^ 6) * |(2 : ℝ) - (-3 / 4)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      _ = (11 / 4 : ℝ) * (C * (1 + |tau| + T) ^ 4 / T ^ 6) := by
        norm_num
        ring
  calc
    ‖∫ u : ℝ in (-3 / 4)..2,
        inghamZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) - (T : ℂ) * I)‖ ≤
        (11 / 4 : ℝ) * (C * (1 + |tau| + T) ^ 4 / T ^ 6) := hintegral
    _ ≤ (11 / 4 : ℝ) * (C * (((2 + |tau|) * T) ^ 4) / T ^ 6) := by
      have hlinear : 1 + |tau| + T ≤ (2 + |tau|) * T := by
        nlinarith [abs_nonneg tau]
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |tau| + T) hlinear 4
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (by positivity))
        (by norm_num)
    _ = D * (T ^ 4 / T ^ 6) := by
      dsimp only [D]
      rw [mul_pow]
      ring

end RHTower.Sieve
