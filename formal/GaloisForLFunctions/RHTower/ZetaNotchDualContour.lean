import GaloisForLFunctions.RHTower.ZetaNotchDualCarrier
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualContourLimit

/-!
# Residue contour for the critical-line product dual weight

The numerator `G_t(−w)·Y^{−w}·e^{w²}` of the critical dual weight is analytic on `Re w > −½`.
Both shifted `χ`-arguments `½ ± it − w` then have real part below `1`, and `G_t(0) = 1`.
Moving the Mellin line from `Re w = 1` to `Re w = −δ` (`0 < δ < ½`) therefore crosses only the
Gaussian pole at zero, whose residue is `1`:

`W_t(Y) = 1 + (1/2π) ∫ G_t(δ − iv) e^{(−δ+iv)²} Y^{δ−iv}/(−δ+iv) dv`
(`critDualWeight_eq_one_add_at_neg`).

The horizontal sides vanish because the Gaussian `e^{−T²}` beats the polynomial growth
`e⁴(1+|t−T|)(1+|t+T|)` of the two `χ`-ratios.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower

/-- The residue numerator of the critical dual weight. -/
def critDualNumerator (t Y : ℝ) (w : ℂ) : ℂ :=
  critCarrier t (-w) * (Y : ℂ) ^ (-w) * Complex.exp (w ^ 2)

/-- The critical dual weight on the Mellin line `Re w = a`. -/
def critDualWeightAt (a t Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    critCarrier t (-((a : ℂ) + (v : ℂ) * I)) * smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I)

theorem critDualWeight_eq_at_one (t Y : ℝ) : critDualWeight t Y = critDualWeightAt 1 t Y := rfl

theorem critCarrier_zero (t : ℝ) : critCarrier t 0 = 1 := by
  unfold critCarrier smoothAFEZetaChiShiftRatio
  rw [add_zero, add_zero, div_self (zetaChi_line_ne_zero t), div_self (zetaChi_line_ne_zero (-t)),
    one_mul]

theorem critDualNumerator_zero (t Y : ℝ) : critDualNumerator t Y 0 = 1 := by
  unfold critDualNumerator
  rw [neg_zero, critCarrier_zero]
  norm_num

/-- One shifted ratio is analytic in the shift on `Re w > −½`. -/
theorem differentiableAt_ratio_neg (τ : ℝ) {w : ℂ} (hw : -1 / 2 < w.re) :
    DifferentiableAt ℂ (fun w : ℂ => smoothAFEZetaChiShiftRatio (linePt τ) (-w)) w := by
  have hGamma : Complex.Gammaℝ (1 - (linePt τ - w)) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    rw [Complex.sub_re, Complex.one_re, Complex.sub_re, linePt_re]
    linarith
  unfold smoothAFEZetaChiShiftRatio
  have hcomp := (zetaChi_analyticAt hGamma).differentiableAt.comp w
    ((differentiableAt_const (c := linePt τ)).add differentiableAt_id.neg)
  simpa [Function.comp_def, sub_eq_add_neg] using hcomp.div_const (zetaChi (linePt τ))

theorem critDualNumerator_analyticOnNhd (t : ℝ) {Y : ℝ} (hY : 0 < Y) :
    AnalyticOnNhd ℂ (critDualNumerator t Y) {w : ℂ | -1 / 2 < w.re} := by
  have hU : IsOpen {w : ℂ | -1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  haveI : NeZero (Y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
  apply DifferentiableOn.analyticOnNhd _ hU
  intro w hw
  have hw' : -1 / 2 < w.re := hw
  have hchi : DifferentiableAt ℂ (fun w : ℂ => critCarrier t (-w)) w := by
    unfold critCarrier
    exact (differentiableAt_ratio_neg t hw').mul (differentiableAt_ratio_neg (-t) hw')
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (Y : ℂ) ^ (-w)) w :=
    (differentiableAt_const_cpow_of_neZero (Y : ℂ) (-w)).comp w differentiableAt_id.neg
  have hexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w ^ 2)) w :=
    Complex.differentiable_exp.differentiableAt.comp w (differentiableAt_id.pow 2)
  have hfun : critDualNumerator t Y =
      ((fun z : ℂ => critCarrier t (-z)) * (fun z : ℂ => (Y : ℂ) ^ (-z))) *
        (fun z : ℂ => Complex.exp (z ^ 2)) := by
    funext z
    simp only [critDualNumerator, Pi.mul_apply]
  rw [hfun]
  exact ((hchi.mul hpow).mul hexp).differentiableWithinAt

theorem critDualIntegrand_eq_numerator_div (t Y : ℝ) (w : ℂ) :
    critCarrier t (-w) * smoothAFEMellinIntegrand Y w = critDualNumerator t Y w * (w - 0)⁻¹ := by
  unfold critDualNumerator smoothAFEMellinIntegrand smoothAFEGaussianKernel
  rw [sub_zero, div_eq_mul_inv]
  ring

/-- Finite-height residue identity. -/
theorem critDualWeight_finite_contour {δ Y T : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (hT : 0 < T) (t : ℝ) :
    RHTower.rectIntegral (fun w : ℂ => critCarrier t (-w) * smoothAFEMellinIntegrand Y w)
        (((-δ : ℝ) : ℂ) - (T : ℂ) * I) (((1 : ℝ) : ℂ) + (T : ℂ) * I) = 2 * Real.pi * I := by
  let z₁ : ℂ := (((-δ : ℝ) : ℂ) - (T : ℂ) * I)
  let z₂ : ℂ := (((1 : ℝ) : ℂ) + (T : ℂ) * I)
  let U : Set ℂ := {w : ℂ | -1 / 2 < w.re}
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    intro w hw
    have hwre := (Complex.mem_reProdIm.mp hw).1
    have hzre : z₁.re = -δ := by simp [z₁]
    have hz2re : z₂.re = 1 := by simp [z₂]
    rw [hzre, hz2re, uIcc_of_le (by linarith)] at hwre
    have hleft : -1 / 2 < -δ := by linarith
    exact hleft.trans_le hwre.1
  have hcauchy := rectIntegral_cauchyFormula_analyticOnNhd (g := critDualNumerator t Y)
    (U := U) (p := 0) (z₁ := z₁) (z₂ := z₂) hsub (critDualNumerator_analyticOnNhd t hY)
    (by simp [z₁]; linarith) (by simp [z₂]) (by simp [z₁]; linarith) (by simp [z₂]; linarith)
  have hfun : (fun w : ℂ => critDualNumerator t Y w * (w - 0)⁻¹) =
      (fun w : ℂ => critCarrier t (-w) * smoothAFEMellinIntegrand Y w) := by
    funext w
    exact (critDualIntegrand_eq_numerator_div t Y w).symm
  rw [hfun, critDualNumerator_zero t Y] at hcauchy
  simpa [z₁, z₂] using hcauchy

/-! ## Integrability on the two vertical lines -/

theorem continuous_critCarrier_line {a : ℝ} (ha : -1 / 2 < a) (t : ℝ) :
    Continuous (fun v : ℝ => critCarrier t (-((a : ℂ) + (v : ℂ) * I))) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hw : -1 / 2 < ((a : ℂ) + (v : ℂ) * I).re := by simpa using ha
  have hd : DifferentiableAt ℂ (fun w : ℂ => critCarrier t (-w)) ((a : ℂ) + (v : ℂ) * I) := by
    unfold critCarrier
    exact (differentiableAt_ratio_neg t hw).mul (differentiableAt_ratio_neg (-t) hw)
  have hf : ContinuousAt (fun v : ℝ => (a : ℂ) + (v : ℂ) * I) v := by fun_prop
  exact ContinuousAt.comp (g := fun w : ℂ => critCarrier t (-w)) hd.continuousAt hf

theorem continuous_smoothAFEMellinIntegrand_line {a Y : ℝ} (ha : a ≠ 0) (hY : 0 < Y) :
    Continuous (fun v : ℝ => smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I)) := by
  haveI : NeZero (Y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
  unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
  apply Continuous.mul
  · exact (continuous_const_cpow (Y : ℂ)).comp (by fun_prop)
  · exact (Complex.continuous_exp.comp (by fun_prop)).div (by fun_prop) (fun v hzero => by
      have hre := congrArg Complex.re hzero
      simp at hre
      exact ha hre)

/-- Envelope on the dual line `Re w = 1`. -/
theorem norm_critDualIntegrand_one_le {Y : ℝ} (hY : 0 < Y) (t v : ℝ) :
    ‖critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      ((1 + |t|) ^ 2 * (Y⁻¹ * Real.exp 1)) * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
  rw [norm_mul]
  have hr := norm_critCarrier_dual_le t v
  have hm := norm_smoothAFEMellinIntegrand_vertical_le hY (show (0 : ℝ) < 1 by norm_num) v
  have hm' : ‖smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
    simpa [Real.rpow_neg_one] using hm
  calc _ ≤ ((1 + |t|) ^ 2 * (1 + |v|) ^ 2) * ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) :=
        mul_le_mul hr hm' (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem integrable_one_add_abs_sq_mul_exp_neg_sq :
    Integrable (fun v : ℝ => (1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
  have h0 : Integrable (fun v : ℝ => Real.exp (-1 * v ^ 2)) := integrable_exp_neg_mul_sq (by norm_num)
  have h1 : Integrable (fun v : ℝ => |v| * Real.exp (-1 * v ^ 2)) := by
    have := (integrable_mul_exp_neg_mul_sq (b := 1) (by norm_num)).norm
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    simp [norm_mul, abs_of_pos (Real.exp_pos _)]
  have h2 : Integrable (fun v : ℝ => v ^ 2 * Real.exp (-1 * v ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := 2) (by norm_num) (by norm_num)
    simpa [Real.rpow_two] using this
  have hsum := (h0.add (h1.const_mul 2)).add h2
  refine hsum.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [Pi.add_apply, neg_mul, one_mul]
  rw [show (1 + |v|) ^ 2 = 1 + 2 * |v| + v ^ 2 by rw [add_sq, sq_abs]; ring]
  ring

theorem critDualWeightAt_one_integrable {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    Integrable (fun v : ℝ => critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  apply Integrable.mono' (integrable_one_add_abs_sq_mul_exp_neg_sq.const_mul
    ((1 + |t|) ^ 2 * (Y⁻¹ * Real.exp 1)))
  · exact ((continuous_critCarrier_line (by norm_num) t).mul
      (continuous_smoothAFEMellinIntegrand_line (by norm_num) hY)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => norm_critDualIntegrand_one_le hY t v

/-- Envelope on the right line `Re w = −δ`. -/
theorem exists_norm_critDualIntegrand_neg_le {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Y : ℝ}, 0 < Y → ∀ t v : ℝ,
      ‖critCarrier t (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y (((-δ : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        K * Y ^ δ / ((max 1 |t - v|) ^ δ * (max 1 |-t - v|) ^ δ) * Real.exp (-(v ^ 2)) := by
  obtain ⟨K, hK, hcar⟩ := exists_norm_critCarrier_right_le hδ hδhalf
  refine ⟨K * (Real.exp (δ ^ 2) / δ), by positivity, fun {Y} hY t v => ?_⟩
  have harg : -(((-δ : ℝ) : ℂ) + (v : ℂ) * I) = ((δ : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [norm_mul, harg]
  have hc := hcar t v
  have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne (σ := -δ) (by linarith) v
  have hpow : ‖(Y : ℂ) ^ (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ = Y ^ δ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    simp
  have hm : ‖smoothAFEMellinIntegrand Y (((-δ : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      Y ^ δ * ((Real.exp (δ ^ 2) / δ) * Real.exp (-(v ^ 2))) := by
    unfold smoothAFEMellinIntegrand
    rw [norm_mul, hpow]
    have hk' : ‖smoothAFEGaussianKernel (((-δ : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        (Real.exp (δ ^ 2) / δ) * Real.exp (-(v ^ 2)) := by
      simpa [neg_sq, abs_neg, abs_of_pos hδ] using hk
    exact mul_le_mul_of_nonneg_left hk' (by positivity)
  have hpos : 0 < (max 1 |t - v|) ^ δ * (max 1 |-t - v|) ^ δ := by
    have h1 : 0 < (max 1 |t - v|) ^ δ := Real.rpow_pos_of_pos (by positivity) _
    have h2 : 0 < (max 1 |-t - v|) ^ δ := Real.rpow_pos_of_pos (by positivity) _
    positivity
  calc _ ≤ K / ((max 1 |t - v|) ^ δ * (max 1 |-t - v|) ^ δ) *
          (Y ^ δ * ((Real.exp (δ ^ 2) / δ) * Real.exp (-(v ^ 2)))) :=
        mul_le_mul hc hm (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

theorem critDualWeightAt_neg_integrable {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (t : ℝ) :
    Integrable (fun v : ℝ => critCarrier t (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y (((-δ : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨K, hK, hb⟩ := exists_norm_critDualIntegrand_neg_le hδ hδhalf
  apply Integrable.mono' ((integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul (K * Y ^ δ))
  · exact ((continuous_critCarrier_line (by linarith) t).mul
      (continuous_smoothAFEMellinIntegrand_line (by linarith) hY)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v => (hb hY t v).trans ?_
    have hden : 1 ≤ (max 1 |t - v|) ^ δ * (max 1 |-t - v|) ^ δ := by
      have h1 : 1 ≤ (max 1 |t - v|) ^ δ := Real.one_le_rpow (le_max_left _ _) hδ.le
      have h2 : 1 ≤ (max 1 |-t - v|) ^ δ := Real.one_le_rpow (le_max_left _ _) hδ.le
      nlinarith
    have hKY : 0 ≤ K * Y ^ δ := by positivity
    simp only [neg_mul, one_mul]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact div_le_self hKY hden

/-! ## The horizontal sides -/

/-- One ratio on a horizontal side, for every abscissa in `[−δ, 1]`. -/
theorem norm_ratio_horizontal_le' (τ : ℝ) {δ u T : ℝ} (hδhalf : δ < 1 / 2) (huLow : -δ ≤ u)
    (huHigh : u ≤ 1) (hheight : 256 ≤ |τ - T|) :
    ‖smoothAFEZetaChiShiftRatio (linePt τ) (-((u : ℂ) + (T : ℂ) * I))‖ ≤
      Real.exp 2 * (1 + |τ - T|) := by
  unfold smoothAFEZetaChiShiftRatio
  rw [norm_div, norm_zetaChi_line, div_one]
  have harg : linePt τ + -((u : ℂ) + (T : ℂ) * I) =
      (((1 / 2 - u : ℝ) : ℂ) + ((τ - T : ℝ) : ℂ) * I) := by
    unfold linePt
    push_cast
    ring
  rw [harg]
  by_cases hu : 0 ≤ u
  · exact norm_zetaChi_le_half_strip (by linarith) (by linarith) (by linarith)
  · have hbase := norm_zetaChi_le_one_right_half_strip (σ := 1 / 2 - u) (t := τ - T)
      (by linarith) (by linarith) hheight
    have hfac : 1 ≤ Real.exp 2 * (1 + |τ - T|) := by
      nlinarith [abs_nonneg (τ - T), Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)]
    exact hbase.trans hfac

theorem norm_critDualIntegrand_horizontal_le {δ Y : ℝ} (hδhalf : δ < 1 / 2) (hY : 0 < Y)
    (t : ℝ) {u T : ℝ} (huLow : -δ ≤ u) (huHigh : u ≤ 1) (hT : 1 ≤ |T|)
    (hh₁ : 256 ≤ |t - T|) (hh₂ : 256 ≤ |-t - T|) :
    ‖critCarrier t (-((u : ℂ) + (T : ℂ) * I)) * smoothAFEMellinIntegrand Y ((u : ℂ) + (T : ℂ) * I)‖
      ≤ (Real.exp 2 * Real.exp 2 * Real.exp |Real.log Y| * Real.exp 1) *
        ((1 + |t - T|) * (1 + |-t - T|) * Real.exp (-(T ^ 2))) := by
  have huLower : -1 ≤ u := by linarith
  have h1 := norm_ratio_horizontal_le' t hδhalf huLow huHigh hh₁
  have h2 := norm_ratio_horizontal_le' (-t) hδhalf huLow huHigh hh₂
  have hpow : ‖(Y : ℂ) ^ (-((u : ℂ) + (T : ℂ) * I))‖ ≤ Real.exp |Real.log Y| := by
    have h := norm_cpow_horizontal_le_exp_abs_log hY (u := -u) (T := -T) (by linarith)
      (by linarith)
    rw [show -((u : ℂ) + (T : ℂ) * I) = ((-u : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I by push_cast; ring]
    exact h
  have hkernel := norm_smoothAFEGaussianKernel_horizontal_le huLower huHigh hT
  unfold critCarrier smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul, norm_mul]
  calc _ ≤ (Real.exp 2 * (1 + |t - T|)) * (Real.exp 2 * (1 + |-t - T|)) *
        (Real.exp |Real.log Y| * (Real.exp 1 * Real.exp (-(T ^ 2)))) := by gcongr
    _ = _ := by ring

theorem tendsto_quadratic_mul_exp_neg_sq (A C : ℝ) :
    Tendsto (fun T : ℝ => C * (1 + A + T) ^ 2 * Real.exp (-(T ^ 2))) atTop (𝓝 0) := by
  have h0 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero 0 (b := 1) (by norm_num)
  have h1 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero 1 (b := 1) (by norm_num)
  have h2 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero 2 (b := 1) (by norm_num)
  have hsum := (h2.add (h1.const_mul (2 * (1 + A)))).add (h0.const_mul ((1 + A) ^ 2))
  have hscaled := hsum.const_mul C
  simpa only [one_mul, add_zero, mul_zero] using hscaled.congr'
    (Filter.Eventually.of_forall fun T => by simp only [one_mul, pow_zero, pow_one]; ring)

theorem tendsto_critDual_horizontal {δ Y : ℝ} (hδhalf : δ < 1 / 2) (hδ : 0 < δ) (hY : 0 < Y)
    (t : ℝ) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-δ)..1,
        critCarrier t (-((u : ℂ) + ((sgn * T : ℝ) : ℂ) * I)) *
          smoothAFEMellinIntegrand Y ((u : ℂ) + ((sgn * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  let B : ℝ := Real.exp 2 * Real.exp 2 * Real.exp |Real.log Y| * Real.exp 1
  have hmajor := tendsto_quadratic_mul_exp_neg_sq |t| (2 * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|t| + 256))] with T hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTlarge : |t| + 256 ≤ T := (le_max_right _ _).trans hT
  have hsT : |sgn * T| = T := by
    rcases hsgn with h | h <;> subst h <;> simp [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)]
  have hsq : (sgn * T) ^ 2 = T ^ 2 := by
    rcases hsgn with h | h <;> subst h <;> ring
  have hh₁ : 256 ≤ |t - sgn * T| := by
    have := abs_sub_abs_le_abs_sub (sgn * T) t
    rw [hsT, abs_sub_comm] at this
    linarith [abs_nonneg t]
  have hh₂ : 256 ≤ |-t - sgn * T| := by
    have := abs_sub_abs_le_abs_sub (sgn * T) (-t)
    rw [hsT, abs_neg, abs_sub_comm] at this
    linarith [abs_nonneg t]
  have hpoint : ∀ u ∈ Set.uIoc (-δ) 1,
      ‖critCarrier t (-((u : ℂ) + ((sgn * T : ℝ) : ℂ) * I)) *
          smoothAFEMellinIntegrand Y ((u : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
        B * ((1 + |t| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : -δ ≤ (1 : ℝ))] at hu
    have hb := norm_critDualIntegrand_horizontal_le hδhalf hY t hu.1.le hu.2
      (by rw [hsT]; exact hT1) hh₁ hh₂
    rw [hsq] at hb
    refine hb.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have ha1 : |t - sgn * T| ≤ |t| + T := by
      calc |t - sgn * T| ≤ |t| + |sgn * T| := abs_sub t (sgn * T)
        _ = |t| + T := by rw [hsT]
    have ha2 : |-t - sgn * T| ≤ |t| + T := by
      calc |-t - sgn * T| ≤ |-t| + |sgn * T| := abs_sub (-t) (sgn * T)
        _ = |t| + T := by rw [hsT, abs_neg]
    have hp1 : 0 ≤ 1 + |t - sgn * T| := by positivity
    have hp2 : 0 ≤ 1 + |-t - sgn * T| := by positivity
    calc (1 + |t - sgn * T|) * (1 + |-t - sgn * T|) ≤ (1 + |t| + T) * (1 + |t| + T) :=
          mul_le_mul (by linarith) (by linarith) hp2 (by positivity)
      _ = (1 + |t| + T) ^ 2 := by ring
  calc ‖∫ u : ℝ in (-δ)..1, critCarrier t (-((u : ℂ) + ((sgn * T : ℝ) : ℂ) * I)) *
          smoothAFEMellinIntegrand Y ((u : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖
      ≤ B * ((1 + |t| + T) ^ 2 * Real.exp (-(T ^ 2))) * |1 - (-δ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ ≤ 2 * B * (1 + |t| + T) ^ 2 * Real.exp (-(T ^ 2)) := by
      have hlen : |1 - (-δ)| ≤ 2 := by rw [abs_of_pos (by linarith)]; linarith
      have hnonneg : 0 ≤ B * ((1 + |t| + T) ^ 2 * Real.exp (-(T ^ 2))) := by positivity
      nlinarith

/-! ## The infinite contour -/

theorem critDual_infinite_contour {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hY : 0 < Y)
    (t : ℝ) :
    I • (∫ v : ℝ, critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
      I • (∫ v : ℝ, critCarrier t (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y (((-δ : ℝ) : ℂ) + (v : ℂ) * I)) = 2 * Real.pi * I := by
  let F : ℂ → ℂ := fun w => critCarrier t (-w) * smoothAFEMellinIntegrand Y w
  have hright : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (critDualWeightAt_one_integrable hY t)
      tendsto_neg_atTop_atBot tendsto_id
  have hleft : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T, F (((-δ : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, F (((-δ : ℝ) : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (critDualWeightAt_neg_integrable hδ hδhalf hY t)
      tendsto_neg_atTop_atBot tendsto_id
  have htop := tendsto_critDual_horizontal hδhalf hδ hY t 1 (Or.inl rfl)
  have hbottom := tendsto_critDual_horizontal hδhalf hδ hY t (-1) (Or.inr rfl)
  have htop' : Tendsto (fun T : ℝ => ∫ u : ℝ in (-δ)..1, F ((u : ℂ) + (T : ℂ) * I)) atTop
      (𝓝 0) := by
    refine htop.congr' (Filter.Eventually.of_forall fun T => ?_)
    simp only [one_mul, F]
  have hbottom' : Tendsto (fun T : ℝ => ∫ u : ℝ in (-δ)..1, F ((u : ℂ) - (T : ℂ) * I)) atTop
      (𝓝 0) := by
    refine hbottom.congr' (Filter.Eventually.of_forall fun T => ?_)
    simp only [F]
    congr 1
    funext u
    push_cast
    ring_nf
  have hlimit := ((hbottom'.sub htop').add (hright.const_smul I)).sub (hleft.const_smul I)
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-δ)..1, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-δ)..1, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, F (((-δ : ℝ) : ℂ) + (v : ℂ) * I)) = 2 * Real.pi * I := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hfinite := critDualWeight_finite_contour hδ hδhalf hY hT t
    simpa [F, RHTower.rectIntegral, sub_eq_add_neg] using hfinite
  have hrhs : Tendsto (fun _T : ℝ => 2 * Real.pi * I) atTop (𝓝 (2 * Real.pi * I)) :=
    tendsto_const_nhds
  have h := tendsto_nhds_unique (hlimit.congr' hevent) hrhs
  simpa [F] using h

/-- **Residue representation**: `W_t(Y) = 1 + W_t^{(−δ)}(Y)`. -/
theorem critDualWeight_eq_one_add_at_neg {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (t : ℝ) :
    critDualWeight t Y = 1 + critDualWeightAt (-δ) t Y := by
  set R : ℂ := ∫ v : ℝ, critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I) with hRdef
  set L : ℂ := ∫ v : ℝ, critCarrier t (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y (((-δ : ℝ) : ℂ) + (v : ℂ) * I) with hLdef
  have hraw := critDual_infinite_contour hδ hδhalf hY t
  have hdiff : R - L = (2 * Real.pi : ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    rw [← hRdef, ← hLdef] at hraw
    simpa [smul_eq_mul, mul_sub, mul_comm] using hraw
  rw [critDualWeight_eq_at_one]
  unfold critDualWeightAt
  rw [← hRdef, ← hLdef, Complex.real_smul, Complex.real_smul]
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  have hR : R = (2 * Real.pi : ℂ) + L := by rw [← hdiff]; ring
  rw [hR]
  push_cast
  field_simp

end RHTower.ZetaNotch
