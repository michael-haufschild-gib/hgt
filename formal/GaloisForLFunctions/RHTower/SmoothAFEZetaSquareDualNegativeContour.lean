import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualWeightDerivativeBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound
import GaloisForLFunctions.RHTower.RectangleCauchyFormulaOn

/-!
# Shifting the square-dual AFE weight to the line Re w = -1/4

The square-dual weight of the smoothed approximate functional equation for `ζ(s)^2`,
`s = 1/2 + iτ`, is `W_τ(Y) = (1/2π) ∫ G(1 + iv) dv` with
`G(w) = (χ(s - w)/χ(s))^2 Y^(-w) e^(w^2) / w`. The numerator of `G` is analytic on `Re w > -1/2`
and equals `1` at `w = 0`, so the only pole between `Re w = -1/4` and `Re w = 1` is the simple pole
at `0` with residue `1`. The module proves the rectangle identity, the Gaussian decay of the
horizontal edges for `Y > 0`, integrability on `Re w = -1/4`, and the resulting identity
`W_τ(Y) = 1 + W_τ^(-1/4)(Y)`.

## Main results

- `smoothAFEZetaSquareDualWeightAt`: the weight integral on the vertical line `Re w = a`.
- `smoothAFEZetaSquareDualNumerator_analyticOnNhd`: the numerator
  `(χ(s - w)/χ(s))^2 Y^(-w) e^(w^2)` is analytic on `Re w > -1/2` for `Y > 0`.
- `smoothAFEZetaSquareDualWeight_finite_contour_quarter`: the rectangle integral of `G` over
  `[-1/4, 1] × [-T, T]` equals `2πi` for `Y, T > 0`.
- `norm_smoothAFEZetaSquareDualIntegrand_horizontal_quarter_le`: an explicit Gaussian bound
  `C_Y (1 + |τ - T|)^2 e^(-T^2)` on the horizontal edges.
- `smoothAFEZetaSquareDual_infinite_contour_quarter`: the line integral on `Re w = 1` minus the one
  on `Re w = -1/4`, both times `i`, equals `2πi`.
- `smoothAFEZetaSquareDualWeight_eq_one_add_at_neg_quarter`: `W_τ(Y) = 1 + W_τ^(-1/4)(Y)`.

## Hypotheses

Unconditional; the analytic statements assume `Y > 0`, and the horizontal edge bound assumes
`-1/4 ≤ u ≤ 1`, `|T| ≥ 1` and `|τ - T| ≥ 256`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-- Square-dual weight on the line `Re w = a`:
`(1/2π) ∫ (χ(s - a - iv)/χ(s))^2 Y^(-(a + iv)) e^((a + iv)^2)/(a + iv) dv`, `s = 1/2 + iτ`. -/
def smoothAFEZetaSquareDualWeightAt (a tau Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    (smoothAFEZetaChiShiftRatio (linePt tau)
      (-((a : ℂ) + (v : ℂ) * I))) ^ 2 *
    smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I)

/-- Numerator `(χ(s - w)/χ(s))^2 Y^(-w) e^(w^2)` of the square-dual integrand, `s = 1/2 + iτ`. -/
def smoothAFEZetaSquareDualNumerator (tau Y : ℝ) (w : ℂ) : ℂ :=
  (smoothAFEZetaChiShiftRatio (linePt tau) (-w)) ^ 2 *
    (Y : ℂ) ^ (-w) * Complex.exp (w ^ 2)

theorem smoothAFEZetaSquareDualWeight_eq_at_one (tau Y : ℝ) :
    smoothAFEZetaSquareDualWeight tau Y =
      smoothAFEZetaSquareDualWeightAt 1 tau Y := by
  rfl

/-- The square-dual numerator equals `1` at `w = 0`, so the residue of the integrand at `0` is `1`. -/
theorem smoothAFEZetaSquareDualNumerator_zero (tau Y : ℝ) :
    smoothAFEZetaSquareDualNumerator tau Y 0 = 1 := by
  unfold smoothAFEZetaSquareDualNumerator smoothAFEZetaChiShiftRatio
  rw [neg_zero, add_zero, div_self (zetaChi_line_ne_zero tau)]
  norm_num

/-- For `Y > 0`, the square-dual numerator is analytic on the half-plane `Re w > -1/2`. -/
theorem smoothAFEZetaSquareDualNumerator_analyticOnNhd
    (tau : ℝ) {Y : ℝ} (hY : 0 < Y) :
    AnalyticOnNhd ℂ (smoothAFEZetaSquareDualNumerator tau Y)
      {w : ℂ | -1 / 2 < w.re} := by
  let U : Set ℂ := {w : ℂ | -1 / 2 < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  haveI : NeZero (Y : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
  apply DifferentiableOn.analyticOnNhd _ hU
  intro w hw
  have hGamma : Gammaℝ (1 - (linePt tau - w)) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    rw [Complex.sub_re, Complex.one_re, Complex.sub_re, linePt_re]
    change -1 / 2 < w.re at hw
    linarith
  have hchi : DifferentiableAt ℂ
      (fun w : ℂ => smoothAFEZetaChiShiftRatio (linePt tau) (-w)) w := by
    unfold smoothAFEZetaChiShiftRatio
    have hcomp := (zetaChi_analyticAt hGamma).differentiableAt.comp w
      ((differentiableAt_const (c := linePt tau)).add differentiableAt_id.neg)
    simpa [Function.comp_def, sub_eq_add_neg] using
      hcomp.div_const (zetaChi (linePt tau))
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (Y : ℂ) ^ (-w)) w :=
    (differentiableAt_const_cpow_of_neZero (Y : ℂ) (-w)).comp w
      differentiableAt_id.neg
  have hexp : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (w ^ 2)) w :=
    Complex.differentiable_exp.differentiableAt.comp w
      (differentiableAt_id.pow 2)
  have hfun : smoothAFEZetaSquareDualNumerator tau Y =
      (((fun z : ℂ => smoothAFEZetaChiShiftRatio (linePt tau) (-z)) ^ 2) *
        (fun z : ℂ => (Y : ℂ) ^ (-z))) *
        (fun z : ℂ => Complex.exp (z ^ 2)) := by
    funext z
    simp only [smoothAFEZetaSquareDualNumerator, Pi.mul_apply, Pi.pow_apply]
  rw [hfun]
  exact (((hchi.pow 2).mul hpow).mul hexp).differentiableWithinAt

theorem smoothAFEZetaSquareDualIntegrand_eq_numerator_div
    (tau Y : ℝ) (w : ℂ) :
    (smoothAFEZetaChiShiftRatio (linePt tau) (-w)) ^ 2 *
        smoothAFEMellinIntegrand Y w =
      smoothAFEZetaSquareDualNumerator tau Y w * (w - 0)⁻¹ := by
  unfold smoothAFEZetaSquareDualNumerator smoothAFEMellinIntegrand
  unfold smoothAFEGaussianKernel
  rw [sub_zero, div_eq_mul_inv]
  ring

/-- For `Y, T > 0`, the boundary integral of the square-dual integrand over the rectangle with
corners `-1/4 - iT` and `1 + iT` equals `2πi` (residue `1` at `w = 0`). -/
theorem smoothAFEZetaSquareDualWeight_finite_contour_quarter
    {Y T : ℝ} (hY : 0 < Y) (hT : 0 < T) (tau : ℝ) :
    rectIntegral
      (fun w : ℂ =>
        (smoothAFEZetaChiShiftRatio (linePt tau) (-w)) ^ 2 *
          smoothAFEMellinIntegrand Y w)
      (((-1 / 4 : ℝ) : ℂ) - (T : ℂ) * I)
      (((1 : ℝ) : ℂ) + (T : ℂ) * I) =
      2 * Real.pi * I := by
  let z1 : ℂ := (((-1 / 4 : ℝ) : ℂ) - (T : ℂ) * I)
  let z2 : ℂ := (((1 : ℝ) : ℂ) + (T : ℂ) * I)
  let U : Set ℂ := {w : ℂ | -1 / 2 < w.re}
  have hsub :
      (uIcc z1.re z2.re ×ℂ uIcc z1.im z2.im) ⊆ U := by
    intro w hw
    have hwre := (Complex.mem_reProdIm.mp hw).1
    have hz1re : z1.re = -1 / 4 := by simp [z1]
    have hz2re : z2.re = 1 := by simp [z2]
    rw [hz1re, hz2re, uIcc_of_le (by norm_num)] at hwre
    exact (by norm_num : (-1 / 2 : ℝ) < -1 / 4).trans_le hwre.1
  have hcauchy := rectIntegral_cauchyFormula_analyticOnNhd
    (g := smoothAFEZetaSquareDualNumerator tau Y)
    (U := U) (p := 0) (z₁ := z1) (z₂ := z2)
    hsub (smoothAFEZetaSquareDualNumerator_analyticOnNhd tau hY)
    (by simp [z1]; norm_num) (by simp [z2])
    (by simp [z1]; linarith) (by simp [z2]; linarith)
  have hfun :
      (fun w : ℂ => smoothAFEZetaSquareDualNumerator tau Y w * (w - 0)⁻¹) =
      (fun w : ℂ =>
        (smoothAFEZetaChiShiftRatio (linePt tau) (-w)) ^ 2 *
          smoothAFEMellinIntegrand Y w) := by
    funext w
    exact (smoothAFEZetaSquareDualIntegrand_eq_numerator_div tau Y w).symm
  rw [hfun] at hcauchy
  rw [smoothAFEZetaSquareDualNumerator_zero tau Y] at hcauchy
  simpa [z1, z2] using hcauchy

/-- For `Y > 0`, the square-dual integrand is integrable along the line `Re w = -1/4`. -/
theorem smoothAFEZetaSquareDualWeightAt_neg_quarter_integrable
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    Integrable (fun v : ℝ =>
      (smoothAFEZetaChiShiftRatio (linePt tau)
        (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
      smoothAFEMellinIntegrand Y
        (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC, hchi⟩ :=
    exists_norm_zetaChi_fixed_right_line_bound
      (σ := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  let D : ℝ := C ^ 2 *
    (Y ^ (1 / 4 : ℝ) * (Real.exp ((1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ)))
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul D)
  · haveI : NeZero (Y : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
    have hratio : Continuous (fun v : ℝ =>
        smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      unfold smoothAFEZetaChiShiftRatio
      apply ContinuousAt.div_const
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Gammaℝ_ne_zero_of_re_pos
        simp [linePt]
        norm_num
    have hmellin : Continuous (fun v : ℝ =>
        smoothAFEMellinIntegrand Y
          (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) := by
      unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
      apply Continuous.mul
      · exact (continuous_const_cpow (Y : ℂ)).comp (by fun_prop)
      · exact (Complex.continuous_exp.comp (by fun_prop)).div
          (by fun_prop) (fun v hzero => by
            have hre := congrArg Complex.re hzero
            norm_num at hre)
    exact ((hratio.pow 2).mul hmellin).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      have harg : linePt tau +
          -(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I) =
          ((3 / 4 : ℝ) : ℂ) + ((tau - v : ℝ) : ℂ) * I := by
        unfold linePt
        push_cast
        ring
      have hr :
          ‖smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ C := by
        unfold smoothAFEZetaChiShiftRatio
        rw [norm_div, norm_zetaChi_line, div_one, harg]
        exact hchi (tau - v)
      have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
        (σ := (-1 / 4 : ℝ)) (by norm_num) v
      have hpow :
          ‖(Y : ℂ) ^ (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ =
            Y ^ (1 / 4 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
        norm_num
      unfold smoothAFEMellinIntegrand
      rw [norm_mul, norm_pow, norm_mul, hpow]
      dsimp only [D]
      calc
        ‖smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ ^ 2 *
            (Y ^ (1 / 4 : ℝ) *
              ‖smoothAFEGaussianKernel
                (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)‖)
          ≤ C ^ 2 *
            (Y ^ (1 / 4 : ℝ) *
              ((Real.exp ((-1 / 4 : ℝ) ^ 2) / |(-1 / 4 : ℝ)|) *
                Real.exp (-(v ^ 2)))) := by gcongr
        _ = D * Real.exp (-1 * v ^ 2) := by
          dsimp only [D]
          norm_num [abs_of_nonneg]
          ring

/-- For `Y > 0`, `-1/4 ≤ u ≤ 1`, `|T| ≥ 1` and `|τ - T| ≥ 256`, the square-dual integrand at
`u + iT` is at most `e^4 e^|log Y| e · (1 + |τ - T|)^2 e^(-T^2)` in norm. -/
theorem norm_smoothAFEZetaSquareDualIntegrand_horizontal_quarter_le
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) {u T : ℝ}
    (huLow : -1 / 4 ≤ u) (huHigh : u ≤ 1)
    (hT : 1 ≤ |T|) (hheight : 256 ≤ |tau - T|) :
    ‖(smoothAFEZetaChiShiftRatio (linePt tau)
          (-((u : ℂ) + (T : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
      (Real.exp 4 * Real.exp |Real.log Y| * Real.exp 1) *
        ((1 + |tau - T|) ^ 2 * Real.exp (-(T ^ 2))) := by
  have hratio :
      ‖smoothAFEZetaChiShiftRatio (linePt tau)
          (-((u : ℂ) + (T : ℂ) * I))‖ ≤
        Real.exp 2 * (1 + |tau - T|) := by
    unfold smoothAFEZetaChiShiftRatio
    rw [norm_div, norm_zetaChi_line, div_one]
    have harg : linePt tau + -((u : ℂ) + (T : ℂ) * I) =
        (((1 / 2 - u : ℝ) : ℂ) +
          ((tau - T : ℝ) : ℂ) * I) := by
      unfold linePt
      push_cast
      ring
    rw [harg]
    by_cases hu : 0 ≤ u
    · exact norm_zetaChi_le_half_strip
        (by linarith) (by linarith) (by linarith)
    · have hbase := norm_zetaChi_le_one_right_half_strip
        (σ := 1 / 2 - u) (t := tau - T)
        (by linarith) (by linarith) hheight
      have hfac : 1 ≤ Real.exp 2 * (1 + |tau - T|) := by
        have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith [abs_nonneg (tau - T), Real.exp_pos 2]
      exact hbase.trans hfac
  have hsingle := norm_smoothAFEZetaDualIntegrand_horizontal_le
    (δ := (1 / 4 : ℝ)) (Y := Y)
    (by norm_num) (by norm_num) hY tau
    (by linarith : -(1 / 4 : ℝ) ≤ u) huHigh hT hheight
  rw [norm_mul, norm_pow]
  calc
    ‖smoothAFEZetaChiShiftRatio (linePt tau)
        (-((u : ℂ) + (T : ℂ) * I))‖ ^ 2 *
        ‖smoothAFEMellinIntegrand Y ((u : ℂ) + (T : ℂ) * I)‖ =
      ‖smoothAFEZetaChiShiftRatio (linePt tau)
        (-((u : ℂ) + (T : ℂ) * I))‖ *
        ‖smoothAFEZetaChiShiftRatio (linePt tau)
            (-((u : ℂ) + (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I)‖ := by
      rw [norm_mul]
      ring
    _ ≤ (Real.exp 2 * (1 + |tau - T|)) *
        ((Real.exp 2 * Real.exp |Real.log Y| * Real.exp 1) *
          ((1 + |tau - T|) * Real.exp (-(T ^ 2)))) := by gcongr
    _ = (Real.exp 4 * Real.exp |Real.log Y| * Real.exp 1) *
        ((1 + |tau - T|) ^ 2 * Real.exp (-(T ^ 2))) := by
      rw [show Real.exp 4 = Real.exp 2 * Real.exp 2 by
        rw [← Real.exp_add]
        norm_num]
      ring

/-- `C (1 + A + T)^2 e^(-T^2) → 0` as `T → ∞`. -/
theorem tendsto_quadratic_mul_exp_neg_sq (A C : ℝ) :
    Tendsto
      (fun T : ℝ =>
        C * (1 + A + T) ^ 2 * Real.exp (-(T ^ 2)))
      atTop (𝓝 0) := by
  have h0 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    0 (b := 1) (by norm_num)
  have h1 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    1 (b := 1) (by norm_num)
  have h2 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    2 (b := 1) (by norm_num)
  have hsum := (h2.add (h1.const_mul (2 * (1 + A)))).add
    (h0.const_mul ((1 + A) ^ 2))
  have hscaled := hsum.const_mul C
  simpa only [one_mul, zero_add, mul_zero, zero_mul, add_zero] using
    hscaled.congr' (Filter.Eventually.of_forall fun T => by ring)

/-- For `Y > 0`, the integral of the square-dual integrand along the top edge `[-1/4, 1] + iT`
tends to `0` as `T → ∞`. -/
theorem tendsto_smoothAFEZetaSquareDual_horizontal_top_quarter
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-1 / 4)..1,
          (smoothAFEZetaChiShiftRatio (linePt tau)
            (-((u : ℂ) + (T : ℂ) * I))) ^ 2 *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ := Real.exp 4 * Real.exp |Real.log Y| * Real.exp 1
  have hmajor : Tendsto (fun T : ℝ =>
      (2 * B) * (1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2)))
      atTop (𝓝 0) := tendsto_quadratic_mul_exp_neg_sq |tau| (2 * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|tau| + 256))] with T hT0
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT0
  have hTlarge : |tau| + 256 ≤ T := (le_max_right _ _).trans hT0
  have hheight : 256 ≤ |tau - T| := by
    rw [abs_of_nonpos (by linarith [le_abs_self tau])]
    linarith [le_abs_self tau]
  have hpoint : ∀ u : ℝ, u ∈ Set.uIoc (-1 / 4) 1 →
      ‖(smoothAFEZetaChiShiftRatio (linePt tau)
          (-((u : ℂ) + (T : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
        B * ((1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 1)] at hu
    have hb := norm_smoothAFEZetaSquareDualIntegrand_horizontal_quarter_le
      hY tau hu.1.le hu.2
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ T)] using hT1)
      hheight
    have hbB :
        ‖(smoothAFEZetaChiShiftRatio (linePt tau)
            (-((u : ℂ) + (T : ℂ) * I))) ^ 2 *
          smoothAFEMellinIntegrand Y ((u : ℂ) + (T : ℂ) * I)‖ ≤
          B * ((1 + |tau - T|) ^ 2 * Real.exp (-(T ^ 2))) := by
      simpa only [B] using hb
    calc
      ‖(smoothAFEZetaChiShiftRatio (linePt tau)
          (-((u : ℂ) + (T : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y ((u : ℂ) + (T : ℂ) * I)‖
        ≤ B * ((1 + |tau - T|) ^ 2 * Real.exp (-(T ^ 2))) := hbB
      _ ≤ B * ((1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
        have hTabs : |T| = T := abs_of_nonneg (by linarith)
        have habs : |tau - T| ≤ |tau| + T := by
          calc
            |tau - T| ≤ |tau| + |T| := abs_sub tau T
            _ = |tau| + T := by rw [hTabs]
        have hone : 1 + |tau - T| ≤ 1 + |tau| + T := by linarith
        have hsquare : (1 + |tau - T|) ^ 2 ≤
            (1 + |tau| + T) ^ 2 := by
          nlinarith [abs_nonneg (tau - T), abs_nonneg tau]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsquare (by positivity)) (by positivity)
  calc
    ‖∫ u : ℝ in (-1 / 4)..1,
        (smoothAFEZetaChiShiftRatio (linePt tau)
          (-((u : ℂ) + (T : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y ((u : ℂ) + (T : ℂ) * I)‖
      ≤ B * ((1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2))) *
          |(1 : ℝ) - (-1 / 4)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ ≤ (2 * B) * (1 + |tau| + T) ^ 2 *
        Real.exp (-(T ^ 2)) := by
      have hlen : |(1 : ℝ) - (-1 / 4)| ≤ 2 := by norm_num
      have hnonneg : 0 ≤ B *
          ((1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2))) := by positivity
      nlinarith

/-- For `Y > 0`, the integral of the square-dual integrand along the bottom edge `[-1/4, 1] - iT`
tends to `0` as `T → ∞`. -/
theorem tendsto_smoothAFEZetaSquareDual_horizontal_bottom_quarter
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-1 / 4)..1,
          (smoothAFEZetaChiShiftRatio (linePt tau)
            (-((u : ℂ) - (T : ℂ) * I))) ^ 2 *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ := Real.exp 4 * Real.exp |Real.log Y| * Real.exp 1
  have hmajor : Tendsto (fun T : ℝ =>
      (2 * B) * (1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2)))
      atTop (𝓝 0) := tendsto_quadratic_mul_exp_neg_sq |tau| (2 * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|tau| + 256))] with T hT0
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT0
  have hTlarge : |tau| + 256 ≤ T := (le_max_right _ _).trans hT0
  have hheight : 256 ≤ |tau + T| := by
    rw [abs_of_nonneg (by linarith [neg_abs_le tau])]
    linarith [neg_abs_le tau]
  have hpoint : ∀ u : ℝ, u ∈ Set.uIoc (-1 / 4) 1 →
      ‖(smoothAFEZetaChiShiftRatio (linePt tau)
          (-((u : ℂ) - (T : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y
          ((u : ℂ) - (T : ℂ) * I)‖ ≤
        B * ((1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 1)] at hu
    have hb := norm_smoothAFEZetaSquareDualIntegrand_horizontal_quarter_le
      hY tau hu.1.le hu.2 (T := -T)
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ T)] using hT1)
      (by simpa using hheight)
    have hb' :
        ‖(smoothAFEZetaChiShiftRatio (linePt tau)
            (-((u : ℂ) - (T : ℂ) * I))) ^ 2 *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I)‖ ≤
          B * ((1 + |tau + T|) ^ 2 * Real.exp (-(T ^ 2))) := by
      simpa [neg_sq, sub_eq_add_neg] using hb
    calc
      ‖(smoothAFEZetaChiShiftRatio (linePt tau)
          (-((u : ℂ) - (T : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y ((u : ℂ) - (T : ℂ) * I)‖
        ≤ B * ((1 + |tau + T|) ^ 2 * Real.exp (-(T ^ 2))) := hb'
      _ ≤ B * ((1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
        have hTabs : |T| = T := abs_of_nonneg (by linarith)
        have habs : |tau + T| ≤ |tau| + T := by
          calc
            |tau + T| ≤ |tau| + |T| := abs_add_le tau T
            _ = |tau| + T := by rw [hTabs]
        have hone : 1 + |tau + T| ≤ 1 + |tau| + T := by linarith
        have hsquare : (1 + |tau + T|) ^ 2 ≤
            (1 + |tau| + T) ^ 2 := by
          nlinarith [abs_nonneg (tau + T), abs_nonneg tau]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsquare (by positivity)) (by positivity)
  calc
    ‖∫ u : ℝ in (-1 / 4)..1,
        (smoothAFEZetaChiShiftRatio (linePt tau)
          (-((u : ℂ) - (T : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y ((u : ℂ) - (T : ℂ) * I)‖
      ≤ B * ((1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2))) *
          |(1 : ℝ) - (-1 / 4)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ ≤ (2 * B) * (1 + |tau| + T) ^ 2 *
        Real.exp (-(T ^ 2)) := by
      have hlen : |(1 : ℝ) - (-1 / 4)| ≤ 2 := by norm_num
      have hnonneg : 0 ≤ B *
          ((1 + |tau| + T) ^ 2 * Real.exp (-(T ^ 2))) := by positivity
      nlinarith

/-- For `Y > 0`, truncated integrals over `Re w = 1`, `|v| ≤ T`, converge to the full line integral. -/
theorem tendsto_smoothAFEZetaSquareDual_right_intervalIntegral
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          (smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
          smoothAFEMellinIntegrand Y
            (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        (smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaSquareDualWeightAt_one_integrable hY tau)
    tendsto_neg_atTop_atBot tendsto_id

/-- For `Y > 0`, truncated integrals over `Re w = -1/4`, `|v| ≤ T`, converge to the full line integral. -/
theorem tendsto_smoothAFEZetaSquareDual_left_intervalIntegral_quarter
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          (smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
          smoothAFEMellinIntegrand Y
            (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        (smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y
          (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaSquareDualWeightAt_neg_quarter_integrable hY tau)
    tendsto_neg_atTop_atBot tendsto_id

/-- Infinite contour shift for `Y > 0`: `i ∫ G(1 + iv) dv - i ∫ G(-1/4 + iv) dv = 2πi`. -/
theorem smoothAFEZetaSquareDual_infinite_contour_quarter
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    I • (∫ v : ℝ,
      (smoothAFEZetaChiShiftRatio (linePt tau)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
      smoothAFEMellinIntegrand Y
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
    I • (∫ v : ℝ,
      (smoothAFEZetaChiShiftRatio (linePt tau)
        (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
      smoothAFEMellinIntegrand Y
        (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I := by
  let F : ℂ → ℂ := fun w =>
    (smoothAFEZetaChiShiftRatio (linePt tau) (-w)) ^ 2 *
      smoothAFEMellinIntegrand Y w
  have hright := tendsto_smoothAFEZetaSquareDual_right_intervalIntegral hY tau
  have hleft := tendsto_smoothAFEZetaSquareDual_left_intervalIntegral_quarter hY tau
  have hbottom := tendsto_smoothAFEZetaSquareDual_horizontal_bottom_quarter hY tau
  have htop := tendsto_smoothAFEZetaSquareDual_horizontal_top_quarter hY tau
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-1 / 4)..1, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1 / 4)..1, F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T,
            F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T,
            F (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝 (I • (∫ v : ℝ, F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ,
          F (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [F, sub_eq_add_neg] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-1 / 4)..1, F ((u : ℂ) - (T : ℂ) * I)) -
        (∫ u : ℝ in (-1 / 4)..1, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T,
          F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T,
          F (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hfinite := smoothAFEZetaSquareDualWeight_finite_contour_quarter
      hY hT tau
    simpa [F, rectIntegral, sub_eq_add_neg] using hfinite
  have hrhs : Tendsto (fun _T : ℝ => 2 * Real.pi * I)
      atTop (𝓝 (2 * Real.pi * I)) := tendsto_const_nhds
  exact tendsto_nhds_unique (hlimit'.congr' hevent) hrhs

/-- For `Y > 0`, the square-dual weight is `1` plus the same weight integral taken on the line
`Re w = -1/4`: `W_τ(Y) = 1 + W_τ^(-1/4)(Y)`. -/
theorem smoothAFEZetaSquareDualWeight_eq_one_add_at_neg_quarter
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    smoothAFEZetaSquareDualWeight tau Y =
      1 + smoothAFEZetaSquareDualWeightAt (-1 / 4) tau Y := by
  let R : ℂ := ∫ v : ℝ,
    (smoothAFEZetaChiShiftRatio (linePt tau)
      (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
    smoothAFEMellinIntegrand Y
      (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  let L : ℂ := ∫ v : ℝ,
    (smoothAFEZetaChiShiftRatio (linePt tau)
      (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
    smoothAFEMellinIntegrand Y
      (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have hraw := smoothAFEZetaSquareDual_infinite_contour_quarter hY tau
  have hdiff : R - L = (2 * Real.pi : ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R, L, smul_eq_mul, mul_sub, mul_assoc, mul_left_comm,
      mul_comm] using hraw
  unfold smoothAFEZetaSquareDualWeight smoothAFEZetaSquareDualWeightAt
  rw [Complex.real_smul, Complex.real_smul]
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * R) =
    1 + (((1 / (2 * Real.pi) : ℝ) : ℂ) * L)
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  have hscale : (((1 / (2 * Real.pi) : ℝ) : ℂ)) =
      (2 * Real.pi : ℂ)⁻¹ := by
    push_cast
    rw [one_div]
  rw [hscale]
  calc
    (2 * Real.pi : ℂ)⁻¹ * R =
        (2 * Real.pi : ℂ)⁻¹ * ((2 * Real.pi : ℂ) + L) := by
      congr 1
      linear_combination hdiff
    _ = 1 + (2 * Real.pi : ℂ)⁻¹ * L := by
      field_simp [hpi]


end RHTower
