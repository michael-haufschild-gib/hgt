import GaloisForLFunctions.RHTower.SmoothAFEZetaDualContour

/-!
# Infinite dual contour shift and small-scale bound

This module passes the exact dual residue rectangle to infinite vertical
lines.  On `Re w=-δ`, `0<δ<1/2`, the shifted χ argument stays strictly
inside the right half of the critical strip, hence is bounded on its fixed
vertical line.  Gaussian decay then yields
`W_τ(Y) = 1 + O_{τ,δ}(Y^δ)`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

theorem norm_smoothAFEZetaChiShiftRatio_neg_right_one_le
    (τ v : ℝ) :
    ‖smoothAFEZetaChiShiftRatio (linePt τ)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
      (1 + |τ|) * (1 + |v|) := by
  unfold smoothAFEZetaChiShiftRatio
  rw [norm_div, norm_zetaChi_line, div_one]
  have harg :
      linePt τ + -(((1 : ℝ) : ℂ) + (v : ℂ) * I) =
        linePt τ + ((-1 : ℂ) + ((-v : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [harg]
  simpa using norm_zetaChi_linePt_add_left_one_le τ (-v)

theorem smoothAFEZetaDualWeightAt_one_integrable
    {Y : ℝ} (hY : 0 < Y) (τ : ℝ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  let D : ℝ := (1 + |τ|) * (Y⁻¹ * Real.exp 1)
  apply Integrable.mono'
    (integrable_one_add_abs_mul_exp_neg_sq.const_mul D)
  · haveI : NeZero (Y : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
    have hratio : Continuous (fun v : ℝ =>
        smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      unfold smoothAFEZetaChiShiftRatio
      apply ContinuousAt.div_const
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        simp [linePt]
        norm_num
    have hmellin : Continuous (fun v : ℝ =>
        smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
      unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
      apply Continuous.mul
      · exact (continuous_const_cpow (Y : ℂ)).comp (by fun_prop)
      · exact (Complex.continuous_exp.comp (by fun_prop)).div
          (by fun_prop) (fun v hzero => by
            have hre := congrArg Complex.re hzero
            norm_num at hre)
    exact (hratio.mul hmellin).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      rw [norm_mul]
      have hr :=
        norm_smoothAFEZetaChiShiftRatio_neg_right_one_le τ v
      have hm := norm_smoothAFEMellinIntegrand_vertical_le
        hY (show (0 : ℝ) < 1 by norm_num) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
            (Y ^ (-(1 : ℝ)) * (Real.exp 1 / 1)) *
              Real.exp (-(v ^ 2)) := by
        simpa using hm
      dsimp only [D]
      calc
        ‖smoothAFEZetaChiShiftRatio (linePt τ) (-(↑(1 : ℝ) + ↑v * I))‖ *
            ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
          ≤ ((1 + |τ|) * (1 + |v|)) *
              ((Y ^ (-(1 : ℝ)) * (Real.exp 1 / 1)) *
                Real.exp (-(v ^ 2))) := by
                  gcongr
        _ = D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
          rw [Real.rpow_neg_one]
          ring

theorem exists_norm_zetaChi_fixed_right_line_bound
    {σ : ℝ} (hσlow : 1 / 2 ≤ σ) (hσhigh : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  let f : ℝ → ℝ := fun t =>
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖
  have hf : Continuous f := by
    apply Continuous.norm
    rw [continuous_iff_continuousAt]
    intro t
    apply (zetaChi_analyticAt ?_).continuousAt.comp
    · fun_prop
    · apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp
      linarith
  have hK : IsCompact (Set.Icc (-256 : ℝ) 256) :=
    isCompact_Icc
  have hKne : (Set.Icc (-256 : ℝ) 256).Nonempty :=
    ⟨0, by norm_num⟩
  obtain ⟨t₀, ht₀, hmax⟩ :=
    hK.exists_isMaxOn hKne hf.continuousOn
  refine ⟨max 1 (f t₀),
    (norm_nonneg _).trans (le_max_right _ _), fun t => ?_⟩
  by_cases ht : 256 ≤ |t|
  · exact (norm_zetaChi_le_one_right_half_strip hσlow hσhigh ht).trans
      (le_max_left _ _)
  · have htmem : t ∈ Set.Icc (-256 : ℝ) 256 := by
      rw [Set.mem_Icc]
      have habs : |t| < 256 := lt_of_not_ge ht
      exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
    exact (hmax htmem).trans (le_max_right _ _)

theorem smoothAFEZetaDualWeightAt_neg_integrable
    {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y
          (((-δ : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC, hchi⟩ :=
    exists_norm_zetaChi_fixed_right_line_bound
      (σ := 1 / 2 + δ) (by linarith) (by linarith)
  let D : ℝ :=
    C * (Y ^ δ * (Real.exp (δ ^ 2) / δ))
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul D)
  · haveI : NeZero (Y : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
    have hratio : Continuous (fun v : ℝ =>
        smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      unfold smoothAFEZetaChiShiftRatio
      apply ContinuousAt.div_const
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        simp [linePt]
        linarith
    have hmellin : Continuous (fun v : ℝ =>
        smoothAFEMellinIntegrand Y
          (((-δ : ℝ) : ℂ) + (v : ℂ) * I)) := by
      unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
      apply Continuous.mul
      · exact (continuous_const_cpow (Y : ℂ)).comp (by fun_prop)
      · exact (Complex.continuous_exp.comp (by fun_prop)).div
          (by fun_prop) (fun v hzero => by
            have hre := congrArg Complex.re hzero
            simp at hre
            linarith)
    exact (hratio.mul hmellin).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      rw [norm_mul]
      have harg :
          linePt τ + -(((-δ : ℝ) : ℂ) + (v : ℂ) * I) =
            (((1 / 2 + δ : ℝ) : ℂ) +
              ((τ - v : ℝ) : ℂ) * I) := by
        unfold linePt
        push_cast
        ring
      have hr :
          ‖smoothAFEZetaChiShiftRatio (linePt τ)
              (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ C := by
        unfold smoothAFEZetaChiShiftRatio
        rw [norm_div, norm_zetaChi_line, div_one, harg]
        exact hchi (τ - v)
      have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
        (σ := -δ) (by linarith) v
      have hpow :
          ‖(Y : ℂ) ^ (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ =
            Y ^ δ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
        simp
      unfold smoothAFEMellinIntegrand
      rw [norm_mul, hpow]
      dsimp only [D]
      change
        ‖smoothAFEZetaChiShiftRatio (linePt τ)
            (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            (Y ^ δ *
              ‖smoothAFEGaussianKernel
                (((-δ : ℝ) : ℂ) + (v : ℂ) * I)‖) ≤
          C * (Y ^ δ * (Real.exp (δ ^ 2) / δ)) *
            Real.exp (-1 * v ^ 2)
      calc
        ‖smoothAFEZetaChiShiftRatio (linePt τ)
            (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            (Y ^ δ * ‖smoothAFEGaussianKernel
              (((-δ : ℝ) : ℂ) + (v : ℂ) * I)‖)
          ≤ C * (Y ^ δ *
              ((Real.exp ((-δ) ^ 2) / |-δ|) *
                Real.exp (-(v ^ 2)))) := by gcongr
        _ = C * (Y ^ δ * (Real.exp (δ ^ 2) / δ)) *
            Real.exp (-1 * v ^ 2) := by
          rw [neg_sq, abs_neg, abs_of_pos hδ]
          ring

theorem norm_smoothAFEZetaDualIntegrand_horizontal_le
    {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) {u T : ℝ}
    (huLow : -δ ≤ u) (huHigh : u ≤ 1)
    (hT : 1 ≤ |T|) (hheight : 256 ≤ |τ - T|) :
    ‖smoothAFEZetaChiShiftRatio (linePt τ)
          (-((u : ℂ) + (T : ℂ) * I)) *
        smoothAFEMellinIntegrand Y
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
      (Real.exp 2 * Real.exp |Real.log Y| * Real.exp 1) *
        ((1 + |τ - T|) * Real.exp (-(T ^ 2))) := by
  have huLower : -1 ≤ u := by linarith
  have hchi :
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
          (-((u : ℂ) + (T : ℂ) * I))‖ ≤
        Real.exp 2 * (1 + |τ - T|) := by
    unfold smoothAFEZetaChiShiftRatio
    rw [norm_div, norm_zetaChi_line, div_one]
    have harg :
        linePt τ + -((u : ℂ) + (T : ℂ) * I) =
          (((1 / 2 - u : ℝ) : ℂ) +
            ((τ - T : ℝ) : ℂ) * I) := by
      unfold linePt
      push_cast
      ring
    rw [harg]
    by_cases hu : 0 ≤ u
    · exact norm_zetaChi_le_half_strip
        (by linarith) (by linarith) (by linarith)
    · have hbase := norm_zetaChi_le_one_right_half_strip
        (σ := 1 / 2 - u) (t := τ - T)
        (by linarith) (by linarith) hheight
      have hexp : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      have hfac : 1 ≤ Real.exp 2 * (1 + |τ - T|) := by
        nlinarith [abs_nonneg (τ - T), Real.exp_pos 2]
      exact hbase.trans hfac
  have hpow :
      ‖(Y : ℂ) ^ (-((u : ℂ) + (T : ℂ) * I))‖ ≤
        Real.exp |Real.log Y| := by
    have h := norm_cpow_horizontal_le_exp_abs_log
      hY (u := -u) (T := -T) (by linarith) (by linarith)
    rw [show -((u : ℂ) + (T : ℂ) * I) =
        ((-u : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I by
      push_cast
      ring]
    exact h
  have hkernel :=
    norm_smoothAFEGaussianKernel_horizontal_le huLower huHigh hT
  unfold smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul]
  calc
    ‖smoothAFEZetaChiShiftRatio (linePt τ) (-(↑u + ↑T * I))‖ *
          (‖(Y : ℂ) ^ (-(↑u + ↑T * I))‖ *
            ‖smoothAFEGaussianKernel (↑u + ↑T * I)‖)
      ≤ (Real.exp 2 * (1 + |τ - T|)) *
          (Real.exp |Real.log Y| *
            (Real.exp 1 * Real.exp (-(T ^ 2)))) := by
        gcongr
    _ = (Real.exp 2 * Real.exp |Real.log Y| * Real.exp 1) *
        ((1 + |τ - T|) * Real.exp (-(T ^ 2))) := by ring

theorem tendsto_linear_mul_exp_neg_sq (A C : ℝ) :
    Tendsto
      (fun T : ℝ =>
        C * (1 + A + T) * Real.exp (-(T ^ 2)))
      atTop (𝓝 0) := by
  have h0 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    0 (b := 1) (by norm_num)
  have h1 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    1 (b := 1) (by norm_num)
  have hsum := h1.add (h0.const_mul (1 + A))
  have hscaled := hsum.const_mul C
  simpa only [one_mul, zero_add, mul_zero] using hscaled.congr'
    (Filter.Eventually.of_forall fun T => by ring)

theorem tendsto_smoothAFEZetaDual_horizontal_top
    {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-δ)..1,
          smoothAFEZetaChiShiftRatio (linePt τ)
              (-((u : ℂ) + (T : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ :=
    Real.exp 2 * Real.exp |Real.log Y| * Real.exp 1
  have hmajor :
      Tendsto (fun T : ℝ =>
        (2 * B) * (1 + |τ| + T) * Real.exp (-(T ^ 2)))
        atTop (𝓝 0) :=
    tendsto_linear_mul_exp_neg_sq |τ| (2 * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|τ| + 256))] with T hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTlarge : |τ| + 256 ≤ T := (le_max_right _ _).trans hT
  have hτle : τ ≤ |τ| := le_abs_self τ
  have hheight : 256 ≤ |τ - T| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hpoint : ∀ u ∈ Set.uIoc (-δ) 1,
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
            (-((u : ℂ) + (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : -δ ≤ (1 : ℝ))] at hu
    have hub : -δ ≤ u ∧ u ≤ 1 := by
      exact ⟨hu.1.le, hu.2⟩
    have hb := norm_smoothAFEZetaDualIntegrand_horizontal_le
      hδ hδhalf hY τ hub.1 hub.2
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ T)] using hT1) hheight
    calc
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
            (-((u : ℂ) + (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I)‖
        ≤ B * ((1 + |τ - T|) * Real.exp (-(T ^ 2))) := hb
      _ ≤ B * ((1 + |τ| + T) * Real.exp (-(T ^ 2))) := by
        have habs : |τ - T| ≤ |τ| + T := by
          have hTabs : |T| = T := abs_of_nonneg (by linarith)
          calc
            |τ - T| ≤ |τ| + |T| := abs_sub τ T
            _ = |τ| + T := by rw [hTabs]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
  calc
    ‖∫ u : ℝ in (-δ)..1,
        smoothAFEZetaChiShiftRatio (linePt τ)
            (-((u : ℂ) + (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) * Real.exp (-(T ^ 2))) *
          |1 - (-δ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ ≤ (2 * B) * (1 + |τ| + T) *
          Real.exp (-(T ^ 2)) := by
      have hlen : |1 - (-δ)| ≤ 2 := by
        rw [abs_of_pos (by linarith)]
        linarith
      have hnonneg :
          0 ≤ B * ((1 + |τ| + T) * Real.exp (-(T ^ 2))) := by
        positivity
      nlinarith

theorem tendsto_smoothAFEZetaDual_horizontal_bottom
    {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-δ)..1,
          smoothAFEZetaChiShiftRatio (linePt τ)
              (-((u : ℂ) - (T : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ :=
    Real.exp 2 * Real.exp |Real.log Y| * Real.exp 1
  have hmajor :
      Tendsto (fun T : ℝ =>
        (2 * B) * (1 + |τ| + T) * Real.exp (-(T ^ 2)))
        atTop (𝓝 0) :=
    tendsto_linear_mul_exp_neg_sq |τ| (2 * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|τ| + 256))] with T hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTlarge : |τ| + 256 ≤ T := (le_max_right _ _).trans hT
  have hτge : -|τ| ≤ τ := neg_abs_le τ
  have hheight : 256 ≤ |τ + T| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hpoint : ∀ u ∈ Set.uIoc (-δ) 1,
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
            (-((u : ℂ) - (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : -δ ≤ (1 : ℝ))] at hu
    have hb := norm_smoothAFEZetaDualIntegrand_horizontal_le
      hδ hδhalf hY τ hu.1.le hu.2
      (T := -T)
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ T)] using hT1)
      (by simpa using hheight)
    have hb' :
        ‖smoothAFEZetaChiShiftRatio (linePt τ)
              (-((u : ℂ) - (T : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              ((u : ℂ) - (T : ℂ) * I)‖ ≤
          B * ((1 + |τ + T|) * Real.exp (-(T ^ 2))) := by
      simpa [neg_sq, sub_eq_add_neg] using hb
    calc
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
            (-((u : ℂ) - (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I)‖
        ≤ B * ((1 + |τ + T|) * Real.exp (-(T ^ 2))) := hb'
      _ ≤ B * ((1 + |τ| + T) * Real.exp (-(T ^ 2))) := by
        have habs : |τ + T| ≤ |τ| + T := by
          have hTabs : |T| = T := abs_of_nonneg (by linarith)
          calc
            |τ + T| ≤ |τ| + |T| := abs_add_le τ T
            _ = |τ| + T := by rw [hTabs]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
  calc
    ‖∫ u : ℝ in (-δ)..1,
        smoothAFEZetaChiShiftRatio (linePt τ)
            (-((u : ℂ) - (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) * Real.exp (-(T ^ 2))) *
          |1 - (-δ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ ≤ (2 * B) * (1 + |τ| + T) *
          Real.exp (-(T ^ 2)) := by
      have hlen : |1 - (-δ)| ≤ 2 := by
        rw [abs_of_pos (by linarith)]
        linarith
      have hnonneg :
          0 ≤ B * ((1 + |τ| + T) * Real.exp (-(T ^ 2))) := by
        positivity
      nlinarith

theorem tendsto_smoothAFEZetaDual_right_intervalIntegral
    {Y : ℝ} (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaChiShiftRatio (linePt τ)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaChiShiftRatio (linePt τ)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            (((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaDualWeightAt_one_integrable hY τ)
    tendsto_neg_atTop_atBot tendsto_id

theorem tendsto_smoothAFEZetaDual_left_intervalIntegral
    {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaChiShiftRatio (linePt τ)
              (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((-δ : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaChiShiftRatio (linePt τ)
            (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            (((-δ : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaDualWeightAt_neg_integrable hδ hδhalf hY τ)
    tendsto_neg_atTop_atBot tendsto_id

theorem smoothAFEZetaDual_infinite_contour
    {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    I • (∫ v : ℝ,
          smoothAFEZetaChiShiftRatio (linePt τ)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
      I • (∫ v : ℝ,
          smoothAFEZetaChiShiftRatio (linePt τ)
              (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((-δ : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I := by
  let F : ℂ → ℂ := fun w =>
    smoothAFEZetaChiShiftRatio (linePt τ) (-w) *
      smoothAFEMellinIntegrand Y w
  have hright := tendsto_smoothAFEZetaDual_right_intervalIntegral hY τ
  have hleft := tendsto_smoothAFEZetaDual_left_intervalIntegral
    hδ hδhalf hY τ
  have hbottom := tendsto_smoothAFEZetaDual_horizontal_bottom
    hδ hδhalf hY τ
  have htop := tendsto_smoothAFEZetaDual_horizontal_top
    hδ hδhalf hY τ
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-δ)..1, F ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (-δ)..1, F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T,
            F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T,
            F (((-δ : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝
        (I • (∫ v : ℝ, F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
          I • (∫ v : ℝ,
            F (((-δ : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [F, sub_eq_add_neg] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-δ)..1, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-δ)..1, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T,
          F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T,
          F (((-δ : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hfinite := smoothAFEZetaDualWeight_finite_contour
      hδ hδhalf hY hT τ
    simpa [F, RHTower.rectIntegral, sub_eq_add_neg] using hfinite
  have hrhs : Tendsto (fun _T : ℝ => 2 * Real.pi * I)
      atTop (𝓝 (2 * Real.pi * I)) := tendsto_const_nhds
  exact tendsto_nhds_unique (hlimit'.congr' hevent) hrhs

/-- Exact small-scale representation of the dual weight. -/
theorem smoothAFEZetaDualWeight_eq_one_add_at_neg
    {δ Y : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    smoothAFEZetaDualWeight τ Y =
      1 + smoothAFEZetaDualWeightAt (-δ) τ Y := by
  let R : ℂ := ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio (linePt τ)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  let L : ℂ := ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio (linePt τ)
        (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((-δ : ℝ) : ℂ) + (v : ℂ) * I)
  have hraw := smoothAFEZetaDual_infinite_contour
    hδ hδhalf hY τ
  have hdiff : R - L = (2 * Real.pi : ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R, L, smul_eq_mul, mul_sub, mul_assoc, mul_left_comm,
      mul_comm] using hraw
  unfold smoothAFEZetaDualWeight smoothAFEZetaDualWeightAt
  rw [Complex.real_smul, Complex.real_smul]
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * R) =
    1 + (((1 / (2 * Real.pi) : ℝ) : ℂ) * L)
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      Real.pi_ne_zero
  have hscale :
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) =
        (2 * Real.pi : ℂ)⁻¹ := by
    push_cast
    rw [one_div]
  rw [hscale]
  calc
    (2 * Real.pi : ℂ)⁻¹ * R =
        (2 * Real.pi : ℂ)⁻¹ * ((2 * Real.pi : ℂ) + L) := by
      congr 1
      calc
        R = (R - L) + L := by ring
        _ = (2 * Real.pi : ℂ) + L := by rw [hdiff]
    _ = 1 + (2 * Real.pi : ℂ)⁻¹ * L := by
      rw [mul_add, inv_mul_cancel₀ hpi]

/-- For every fixed `τ` and `0<δ<1/2`, the exact dual weight differs from
one by `O(Y^δ)` at small scale. -/
theorem exists_norm_smoothAFEZetaDualWeight_sub_one_le_rpow
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℝ) {Y : ℝ}, 0 < Y →
      ‖smoothAFEZetaDualWeight τ Y - 1‖ ≤ K * Y ^ δ := by
  obtain ⟨C, hC, hchi⟩ :=
    exists_norm_zetaChi_fixed_right_line_bound
      (σ := 1 / 2 + δ) (by linarith) (by linarith)
  let G : ℝ := ∫ v : ℝ, Real.exp (-(v ^ 2))
  let K : ℝ :=
    (1 / (2 * Real.pi)) *
      C * (Real.exp (δ ^ 2) / δ) * G
  have hG : 0 ≤ G :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, fun τ {Y} hY => ?_⟩
  have hweight := smoothAFEZetaDualWeight_eq_one_add_at_neg
    hδ hδhalf hY τ
  have hdiff :
      smoothAFEZetaDualWeight τ Y - 1 =
        smoothAFEZetaDualWeightAt (-δ) τ Y := by
    rw [hweight]
    ring
  rw [hdiff]
  let f : ℝ → ℂ := fun v =>
    smoothAFEZetaChiShiftRatio (linePt τ)
        (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((-δ : ℝ) : ℂ) + (v : ℂ) * I)
  let D : ℝ := C * (Y ^ δ * (Real.exp (δ ^ 2) / δ))
  have hf : Integrable f :=
    smoothAFEZetaDualWeightAt_neg_integrable hδ hδhalf hY τ
  have hmajor : Integrable (fun v : ℝ =>
      D * Real.exp (-(v ^ 2))) :=
    by
      simpa [one_mul] using
        (integrable_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1)).const_mul D
  have hpoint : ∀ v : ℝ, ‖f v‖ ≤
      D * Real.exp (-(v ^ 2)) := by
    intro v
    have harg :
        linePt τ + -(((-δ : ℝ) : ℂ) + (v : ℂ) * I) =
          (((1 / 2 + δ : ℝ) : ℂ) +
            ((τ - v : ℝ) : ℂ) * I) := by
      unfold linePt
      push_cast
      ring
    have hr :
        ‖smoothAFEZetaChiShiftRatio (linePt τ)
            (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ C := by
      unfold smoothAFEZetaChiShiftRatio
      rw [norm_div, norm_zetaChi_line, div_one, harg]
      exact hchi (τ - v)
    have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
      (σ := -δ) (by linarith) v
    have hpow :
        ‖(Y : ℂ) ^ (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ =
          Y ^ δ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      simp
    dsimp only [f, D]
    unfold smoothAFEMellinIntegrand
    rw [norm_mul, norm_mul, hpow]
    calc
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          (Y ^ δ * ‖smoothAFEGaussianKernel
            (((-δ : ℝ) : ℂ) + (v : ℂ) * I)‖)
        ≤ C * (Y ^ δ *
            ((Real.exp ((-δ) ^ 2) / |-δ|) *
              Real.exp (-(v ^ 2)))) := by gcongr
      _ = C * (Y ^ δ * (Real.exp (δ ^ 2) / δ)) *
          Real.exp (-(v ^ 2)) := by
        rw [neg_sq, abs_neg, abs_of_pos hδ]
        ring
  unfold smoothAFEZetaDualWeightAt
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) * ‖∫ v : ℝ, f v‖
      ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, ‖f v‖ := by
        exact mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm f) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
          ∫ v : ℝ, D * Real.exp (-(v ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply integral_mono_ae hf.norm hmajor
        exact Filter.Eventually.of_forall hpoint
    _ = K * Y ^ δ := by
      rw [integral_const_mul]
      dsimp only [K, D, G]
      ring

/-- Positive-line tail bound for the exact dual weight. -/
theorem exists_norm_smoothAFEZetaDualWeight_le_inv
    : ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℝ) {Y : ℝ}, 0 < Y →
      ‖smoothAFEZetaDualWeight τ Y‖ ≤
        K * (1 + |τ|) * Y⁻¹ := by
  let G : ℝ :=
    ∫ v : ℝ, (1 + |v|) * Real.exp (-(v ^ 2))
  let K : ℝ := (1 / (2 * Real.pi)) * Real.exp 1 * G
  have hG : 0 ≤ G := integral_nonneg fun v => by positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, fun τ {Y} hY => ?_⟩
  let f : ℝ → ℂ := fun v =>
    smoothAFEZetaChiShiftRatio (linePt τ)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  let D : ℝ := (1 + |τ|) * (Y⁻¹ * Real.exp 1)
  have hf : Integrable f :=
    smoothAFEZetaDualWeightAt_one_integrable hY τ
  have hmajor : Integrable (fun v : ℝ =>
      D * ((1 + |v|) * Real.exp (-(v ^ 2)))) :=
    integrable_one_add_abs_mul_exp_neg_sq.const_mul D
  have hpoint : ∀ v : ℝ,
      ‖f v‖ ≤ D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
    intro v
    have hr :=
      norm_smoothAFEZetaChiShiftRatio_neg_right_one_le τ v
    have hm := norm_smoothAFEMellinIntegrand_vertical_le
      hY (show (0 : ℝ) < 1 by norm_num) v
    have hm' :
        ‖smoothAFEMellinIntegrand Y
            (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
          (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
      simpa [Real.rpow_neg_one] using hm
    dsimp only [f, D]
    rw [norm_mul]
    calc
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
          (-(↑(1 : ℝ) + ↑v * I))‖ *
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
        ≤ ((1 + |τ|) * (1 + |v|)) *
            ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by
          gcongr
      _ = (1 + |τ|) * (Y⁻¹ * Real.exp 1) *
          ((1 + |v|) * Real.exp (-(v ^ 2))) := by ring
  unfold smoothAFEZetaDualWeight
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) * ‖∫ v : ℝ, f v‖
      ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, ‖f v‖ := by
        exact mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm f) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
          ∫ v : ℝ,
            D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply integral_mono_ae hf.norm hmajor
        exact Filter.Eventually.of_forall hpoint
    _ = K * (1 + |τ|) * Y⁻¹ := by
      rw [integral_const_mul]
      dsimp only [K, D, G]
      ring

end RHTower
