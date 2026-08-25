import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualContour

/-!
# Infinite displaced dual contour and conductor localization

Gaussian decay passes the displaced residue rectangle to infinite vertical
lines.  The negative edge then gives the exact conductor-sensitive
small-scale expansion of the dual weight.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

theorem smoothAFEZetaDisplacedDualWeightAt_one_integrable
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    {Y : ℝ} (hY : 0 < Y) (τ : ℝ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  have hσ0 : -1 / 2 - d ≠ 0 := by linarith
  obtain ⟨C, hC0, hchi⟩ := exists_bound_norm_zetaChi_vertical hσ0
    (by linarith : -1 ≤ -1 / 2 - d) (by linarith : -1 / 2 - d ≤ 1 / 2)
  let B : ℝ := ‖(zetaChi (displacedLinePt d τ))⁻¹‖
  let D : ℝ := C * B * (Y⁻¹ * Real.exp 1)
  apply Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (1 + |τ|) 2).const_mul D)
  · haveI : NeZero (Y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
    have hratio : Continuous (fun v : ℝ =>
        smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      unfold smoothAFEZetaChiShiftRatio
      apply ContinuousAt.div_const
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        simp [displacedLinePt]
        linarith
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
      have harg :
          displacedLinePt d τ +
              -(((1 : ℝ) : ℂ) + (v : ℂ) * I) =
            (((-1 / 2 - d : ℝ) : ℂ) +
              ((τ - v : ℝ) : ℂ) * I) := by
        unfold displacedLinePt
        push_cast
        ring
      have hr :
          ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
            C * (1 + |τ| + |v|) ^ 2 * B := by
        unfold smoothAFEZetaChiShiftRatio
        rw [div_eq_mul_inv, norm_mul, harg]
        have hbase := hchi (τ - v)
        have habs : 1 + |τ - v| ≤ 1 + |τ| + |v| := by
          linarith [abs_sub τ v]
        have hsq : (1 + |τ - v|) ^ 2 ≤ (1 + |τ| + |v|) ^ 2 := by
          nlinarith [abs_nonneg (τ - v), abs_nonneg τ, abs_nonneg v]
        exact mul_le_mul_of_nonneg_right
          (hbase.trans (mul_le_mul_of_nonneg_left hsq hC0)) (norm_nonneg _)
      have hm := norm_smoothAFEMellinIntegrand_vertical_le
        hY (show (0 : ℝ) < 1 by norm_num) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
            (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
        simpa [Real.rpow_neg_one] using hm
      dsimp only [D]
      calc
        ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
              (-(↑(1 : ℝ) + ↑v * I))‖ *
            ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
          ≤ (C * (1 + |τ| + |v|) ^ 2 * B) *
              ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
        _ = C * B * (Y⁻¹ * Real.exp 1) *
              ((1 + |τ| + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by ring

theorem smoothAFEZetaDisplacedDualWeightAt_neg_integrable
    {d η : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    {Y : ℝ} (hY : 0 < Y) (τ : ℝ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y
          (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨K, hK0, hratioBound⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_displaced_le hd hdhalf hη hηhalf
  let δ : ℝ := d + η
  let D : ℝ :=
    (K / (max 1 |τ|) ^ δ) *
      (Y ^ δ * (Real.exp (δ ^ 2) / δ))
  apply Integrable.mono'
    (integrable_one_add_abs_mul_exp_neg_sq.const_mul D)
  · haveI : NeZero (Y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
    have hratio : Continuous (fun v : ℝ =>
        smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      unfold smoothAFEZetaChiShiftRatio
      apply ContinuousAt.div_const
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        dsimp only [δ]
        simp [displacedLinePt]
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
            dsimp only [δ] at hre
            linarith)
    exact (hratio.mul hmellin).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      have hr := hratioBound τ v
      have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
        (σ := -(d + η)) (by linarith) v
      have hpow :
          ‖(Y : ℂ) ^ (-((((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)))‖ =
            Y ^ (d + η) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
        simp
      have hvbase : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
      have hvpow : (1 + |v|) ^ η ≤ 1 + |v| := by
        simpa using Real.rpow_le_rpow_of_exponent_le hvbase (by linarith : η ≤ 1)
      unfold smoothAFEMellinIntegrand
      rw [norm_mul, norm_mul, hpow]
      dsimp only [D, δ]
      calc
        ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
            (-(((-((d + η)) : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            (Y ^ (d + η) *
              ‖smoothAFEGaussianKernel
                (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)‖)
          ≤ (K * (1 + |v|) ^ η / (max 1 |τ|) ^ (d + η)) *
              (Y ^ (d + η) *
                ((Real.exp ((-(d + η)) ^ 2) / |-(d + η)|) *
                  Real.exp (-(v ^ 2)))) := by gcongr
        _ ≤ (K * (1 + |v|) / (max 1 |τ|) ^ (d + η)) *
              (Y ^ (d + η) *
                ((Real.exp ((-(d + η)) ^ 2) / |-(d + η)|) *
                  Real.exp (-(v ^ 2)))) := by gcongr
        _ = (K / (max 1 |τ|) ^ (d + η)) *
              (Y ^ (d + η) * (Real.exp ((d + η) ^ 2) / (d + η))) *
              ((1 + |v|) * Real.exp (-(v ^ 2))) := by
          rw [neg_sq, abs_neg, abs_of_pos (by linarith : 0 < d + η)]
          ring

theorem norm_smoothAFEZetaDisplacedDualIntegrand_horizontal_le
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (_hη : 0 < η) (hηhalf : η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) {u T : ℝ}
    (huLow : -(d + η) ≤ u) (huHigh : u ≤ 1)
    (hT : 1 ≤ |T|) (hheight : 256 ≤ |τ - T|) :
    ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-((u : ℂ) + (T : ℂ) * I)) *
        smoothAFEMellinIntegrand Y
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
      ((Real.exp 4 + Real.exp 2 + 1) *
          ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
          Real.exp |Real.log Y| * Real.exp 1) *
        ((1 + |τ - T|) ^ 2 * Real.exp (-(T ^ 2))) := by
  have hδlt : d + η < 1 := by linarith
  have huLower : -1 ≤ u := by linarith
  have hchiNum :
      ‖zetaChi (displacedLinePt d τ -
          ((u : ℂ) + (T : ℂ) * I))‖ ≤
        (Real.exp 4 + Real.exp 2 + 1) * (1 + |τ - T|) ^ 2 := by
    have harg : displacedLinePt d τ - ((u : ℂ) + (T : ℂ) * I) =
        (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - T : ℝ) : ℂ) * I) := by
      unfold displacedLinePt
      push_cast
      ring
    rw [harg]
    by_cases hleft : 1 / 2 - d - u ≤ -1 / 2
    · have hbase := norm_zetaChi_le_negative_one_strip
        (σ := 1 / 2 - d - u) (t := τ - T)
        (by linarith) hleft (by linarith)
      have hpow : 1 + |τ - T| ≤ (1 + |τ - T|) ^ 2 := by
        nlinarith [abs_nonneg (τ - T)]
      calc
        ‖zetaChi (↑(1 / 2 - d - u) + ↑(τ - T) * I)‖
            ≤ Real.exp 4 * (1 + |τ - T|) ^ 2 := hbase
        _ ≤ (Real.exp 4 + Real.exp 2 + 1) *
              (1 + |τ - T|) ^ 2 := by
          nlinarith [sq_nonneg (1 + |τ - T|), Real.exp_pos 2]
    · by_cases hright : 1 / 2 ≤ 1 / 2 - d - u
      · have hbase := norm_zetaChi_le_one_right_half_strip
          (σ := 1 / 2 - d - u) (t := τ - T)
          hright (by linarith) hheight
        have hsq : 1 ≤ (1 + |τ - T|) ^ 2 := by
          nlinarith [abs_nonneg (τ - T)]
        calc
          ‖zetaChi (↑(1 / 2 - d - u) + ↑(τ - T) * I)‖ ≤ 1 := hbase
          _ ≤ (Real.exp 4 + Real.exp 2 + 1) *
                (1 + |τ - T|) ^ 2 := by
            have : 1 ≤ Real.exp 4 + Real.exp 2 + 1 := by
              nlinarith [Real.exp_pos 4, Real.exp_pos 2]
            nlinarith
      · have hbase := norm_zetaChi_le_half_strip
          (σ := 1 / 2 - d - u) (t := τ - T)
          (by linarith) (by linarith) (by linarith)
        have hlin : 1 + |τ - T| ≤ (1 + |τ - T|) ^ 2 := by
          nlinarith [abs_nonneg (τ - T)]
        calc
          ‖zetaChi (↑(1 / 2 - d - u) + ↑(τ - T) * I)‖
              ≤ Real.exp 2 * (1 + |τ - T|) := hbase
          _ ≤ Real.exp 2 * (1 + |τ - T|) ^ 2 := by gcongr
          _ ≤ (Real.exp 4 + Real.exp 2 + 1) *
                (1 + |τ - T|) ^ 2 := by
            nlinarith [sq_nonneg (1 + |τ - T|), Real.exp_pos 4]
  have hratio :
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-((u : ℂ) + (T : ℂ) * I))‖ ≤
        ((Real.exp 4 + Real.exp 2 + 1) * (1 + |τ - T|) ^ 2) *
          ‖(zetaChi (displacedLinePt d τ))⁻¹‖ := by
    unfold smoothAFEZetaChiShiftRatio
    rw [div_eq_mul_inv, norm_mul, sub_eq_add_neg]
    exact mul_le_mul_of_nonneg_right hchiNum (norm_nonneg _)
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
    ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(↑u + ↑T * I))‖ *
        (‖(Y : ℂ) ^ (-(↑u + ↑T * I))‖ *
          ‖smoothAFEGaussianKernel (↑u + ↑T * I)‖)
      ≤ (((Real.exp 4 + Real.exp 2 + 1) * (1 + |τ - T|) ^ 2) *
          ‖(zetaChi (displacedLinePt d τ))⁻¹‖) *
        (Real.exp |Real.log Y| *
          (Real.exp 1 * Real.exp (-(T ^ 2)))) := by gcongr
    _ = ((Real.exp 4 + Real.exp 2 + 1) *
          ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
          Real.exp |Real.log Y| * Real.exp 1) *
        ((1 + |τ - T|) ^ 2 * Real.exp (-(T ^ 2))) := by ring

theorem tendsto_smoothAFEZetaDisplacedDual_horizontal_top
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-(d + η))..1,
          smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
              (-((u : ℂ) + (T : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ :=
    (Real.exp 4 + Real.exp 2 + 1) *
      ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
      Real.exp |Real.log Y| * Real.exp 1
  have hmajor :
      Tendsto (fun T : ℝ =>
        (2 * B) * (1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2)))
        atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using
      (tendsto_shifted_pow_mul_exp_neg_sq (1 + |τ|) 2).const_mul (2 * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|τ| + 256))] with T hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTlarge : |τ| + 256 ≤ T := (le_max_right _ _).trans hT
  have hheight : 256 ≤ |τ - T| := by
    rw [abs_of_nonpos (by linarith [le_abs_self τ])]
    linarith [le_abs_self τ]
  have hpoint : ∀ u ∈ Set.uIoc (-(d + η)) 1,
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
            (-((u : ℂ) + (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : -(d + η) ≤ (1 : ℝ))] at hu
    have hb := norm_smoothAFEZetaDisplacedDualIntegrand_horizontal_le
      hd hdhalf hη hηhalf hY τ hu.1.le hu.2
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ T)] using hT1) hheight
    calc
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
            (-((u : ℂ) + (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I)‖
          ≤ B * ((1 + |τ - T|) ^ 2 * Real.exp (-(T ^ 2))) := hb
      _ ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
        have habs : |τ - T| ≤ |τ| + T := by
          have hTabs : |T| = T := abs_of_nonneg (by linarith)
          calc
            |τ - T| ≤ |τ| + |T| := abs_sub τ T
            _ = |τ| + T := by rw [hTabs]
        have hsq : (1 + |τ - T|) ^ 2 ≤ (1 + |τ| + T) ^ 2 := by
          nlinarith [abs_nonneg (τ - T), abs_nonneg τ]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le)
          (by positivity)
  calc
    ‖∫ u : ℝ in (-(d + η))..1,
        smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
            (-((u : ℂ) + (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) *
          |1 - (-(d + η))| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ ≤ (2 * B) * (1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2)) := by
      have hlen : |1 - (-(d + η))| ≤ 2 := by
        rw [abs_of_pos (by linarith)]
        linarith
      have hnonneg :
          0 ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
        positivity
      nlinarith

theorem tendsto_smoothAFEZetaDisplacedDual_horizontal_bottom
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-(d + η))..1,
          smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
              (-((u : ℂ) - (T : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ :=
    (Real.exp 4 + Real.exp 2 + 1) *
      ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
      Real.exp |Real.log Y| * Real.exp 1
  have hmajor :
      Tendsto (fun T : ℝ =>
        (2 * B) * (1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2)))
        atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using
      (tendsto_shifted_pow_mul_exp_neg_sq (1 + |τ|) 2).const_mul (2 * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|τ| + 256))] with T hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTlarge : |τ| + 256 ≤ T := (le_max_right _ _).trans hT
  have hheight : 256 ≤ |τ + T| := by
    rw [abs_of_nonneg (by linarith [neg_abs_le τ])]
    linarith [neg_abs_le τ]
  have hpoint : ∀ u ∈ Set.uIoc (-(d + η)) 1,
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
            (-((u : ℂ) - (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : -(d + η) ≤ (1 : ℝ))] at hu
    have hb := norm_smoothAFEZetaDisplacedDualIntegrand_horizontal_le
      hd hdhalf hη hηhalf hY τ hu.1.le hu.2
      (T := -T)
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ T)] using hT1)
      (by simpa using hheight)
    have hb' :
        ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
              (-((u : ℂ) - (T : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              ((u : ℂ) - (T : ℂ) * I)‖ ≤
          B * ((1 + |τ + T|) ^ 2 * Real.exp (-(T ^ 2))) := by
      simpa [B, neg_sq, sub_eq_add_neg] using hb
    calc
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
            (-((u : ℂ) - (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I)‖
          ≤ B * ((1 + |τ + T|) ^ 2 * Real.exp (-(T ^ 2))) := hb'
      _ ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
        have habs : |τ + T| ≤ |τ| + T := by
          have hTabs : |T| = T := abs_of_nonneg (by linarith)
          calc
            |τ + T| ≤ |τ| + |T| := abs_add_le τ T
            _ = |τ| + T := by rw [hTabs]
        have hsq : (1 + |τ + T|) ^ 2 ≤ (1 + |τ| + T) ^ 2 := by
          nlinarith [abs_nonneg (τ + T), abs_nonneg τ]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le)
          (by positivity)
  calc
    ‖∫ u : ℝ in (-(d + η))..1,
        smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
            (-((u : ℂ) - (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) *
          |1 - (-(d + η))| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ ≤ (2 * B) * (1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2)) := by
      have hlen : |1 - (-(d + η))| ≤ 2 := by
        rw [abs_of_pos (by linarith)]
        linarith
      have hnonneg :
          0 ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
        positivity
      nlinarith

theorem tendsto_smoothAFEZetaDisplacedDual_right_intervalIntegral
    {d Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            (((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaDisplacedDualWeightAt_one_integrable hd hdhalf hY τ)
    tendsto_neg_atTop_atBot tendsto_id

theorem tendsto_smoothAFEZetaDisplacedDual_left_intervalIntegral
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
              (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
            (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaDisplacedDualWeightAt_neg_integrable
      hd hdhalf hη hηhalf hY τ)
    tendsto_neg_atTop_atBot tendsto_id

theorem smoothAFEZetaDisplacedDual_infinite_contour
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    I • (∫ v : ℝ,
          smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
      I • (∫ v : ℝ,
          smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
              (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I := by
  let F : ℂ → ℂ := fun w =>
    smoothAFEZetaChiShiftRatio (displacedLinePt d τ) (-w) *
      smoothAFEMellinIntegrand Y w
  have hright := tendsto_smoothAFEZetaDisplacedDual_right_intervalIntegral
    hd hdhalf hY τ
  have hleft := tendsto_smoothAFEZetaDisplacedDual_left_intervalIntegral
    hd hdhalf hη hηhalf hY τ
  have hbottom := tendsto_smoothAFEZetaDisplacedDual_horizontal_bottom
    hd hdhalf hη hηhalf hY τ
  have htop := tendsto_smoothAFEZetaDisplacedDual_horizontal_top
    hd hdhalf hη hηhalf hY τ
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-(d + η))..1,
              F ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (-(d + η))..1,
              F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T,
            F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T,
            F (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝
        (I • (∫ v : ℝ,
              F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
          I • (∫ v : ℝ,
            F (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [F, sub_eq_add_neg] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-(d + η))..1,
            F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-(d + η))..1,
            F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T,
          F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T,
          F (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hfinite := smoothAFEZetaDisplacedDualWeight_finite_contour
      hd hdhalf hη hηhalf hY hT τ
    simpa [F, RHTower.rectIntegral, sub_eq_add_neg] using hfinite
  have hrhs : Tendsto (fun _T : ℝ => 2 * Real.pi * I)
      atTop (𝓝 (2 * Real.pi * I)) := tendsto_const_nhds
  exact tendsto_nhds_unique (hlimit'.congr' hevent) hrhs

/-- Exact negative-contour representation at the displaced abscissa. -/
theorem smoothAFEZetaDisplacedDualWeight_eq_one_add_at_neg
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    smoothAFEZetaDisplacedDualWeight d τ Y =
      1 + smoothAFEZetaDisplacedDualWeightAt (-(d + η)) d τ Y := by
  let R : ℂ := ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  let L : ℂ := ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
        (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)
  have hraw := smoothAFEZetaDisplacedDual_infinite_contour
    hd hdhalf hη hηhalf hY τ
  have hdiff : R - L = (2 * Real.pi : ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R, L, smul_eq_mul, mul_sub, mul_assoc, mul_left_comm,
      mul_comm] using hraw
  unfold smoothAFEZetaDisplacedDualWeight
    smoothAFEZetaDisplacedDualWeightAt
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

/-- Conductor-localized small-scale estimate at `1/2-d+iτ`. -/
theorem exists_norm_smoothAFEZetaDisplacedDualWeight_sub_one_le_conductor
    {d η : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) {Y : ℝ}, 0 < Y →
      ‖smoothAFEZetaDisplacedDualWeight d τ Y - 1‖ ≤
        C * Y ^ (d + η) / (max 1 |τ|) ^ (d + η) := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_displaced_le
      hd hdhalf hη hηhalf
  let G : ℝ :=
    ∫ v : ℝ, (1 + |v|) * Real.exp (-(v ^ 2))
  let C : ℝ :=
    (1 / (2 * Real.pi)) * K *
      (Real.exp ((d + η) ^ 2) / (d + η)) * G
  have hG : 0 ≤ G := integral_nonneg fun v => by positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun τ {Y} hY => ?_⟩
  have hweight :=
    smoothAFEZetaDisplacedDualWeight_eq_one_add_at_neg
      hd hdhalf hη hηhalf hY τ
  have hdiff :
      smoothAFEZetaDisplacedDualWeight d τ Y - 1 =
        smoothAFEZetaDisplacedDualWeightAt (-(d + η)) d τ Y := by
    rw [hweight]
    ring
  rw [hdiff]
  let f : ℝ → ℂ := fun v =>
    smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
        (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)
  let D : ℝ :=
    K * (Y ^ (d + η) / (max 1 |τ|) ^ (d + η)) *
      (Real.exp ((d + η) ^ 2) / (d + η))
  have hf : Integrable f :=
    smoothAFEZetaDisplacedDualWeightAt_neg_integrable
      hd hdhalf hη hηhalf hY τ
  have hmajor : Integrable (fun v : ℝ =>
      D * ((1 + |v|) * Real.exp (-(v ^ 2)))) :=
    integrable_one_add_abs_mul_exp_neg_sq.const_mul D
  have hpoint : ∀ v : ℝ,
      ‖f v‖ ≤ D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
    intro v
    have hr := hratio τ v
    have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
      (σ := -(d + η)) (by linarith) v
    have hpow :
        ‖(Y : ℂ) ^ (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ =
          Y ^ (d + η) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      simp
    have hvbase : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hvpow : (1 + |v|) ^ η ≤ 1 + |v| := by
      simpa using
        Real.rpow_le_rpow_of_exponent_le hvbase (by linarith : η ≤ 1)
    have hqpos : 0 < (max 1 |τ|) ^ (d + η) :=
      Real.rpow_pos_of_pos
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (d + η)
    dsimp only [f, D]
    unfold smoothAFEMellinIntegrand
    rw [norm_mul, norm_mul, hpow]
    calc
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          (Y ^ (d + η) *
            ‖smoothAFEGaussianKernel
              (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)‖)
        ≤ (K * (1 + |v|) ^ η / (max 1 |τ|) ^ (d + η)) *
            (Y ^ (d + η) *
              ((Real.exp ((-(d + η)) ^ 2) / |-(d + η)|) *
                Real.exp (-(v ^ 2)))) := by
          gcongr
      _ ≤ (K * (1 + |v|) / (max 1 |τ|) ^ (d + η)) *
            (Y ^ (d + η) *
              ((Real.exp ((-(d + η)) ^ 2) / |-(d + η)|) *
                Real.exp (-(v ^ 2)))) := by
          gcongr
      _ = K * (Y ^ (d + η) / (max 1 |τ|) ^ (d + η)) *
            (Real.exp ((d + η) ^ 2) / (d + η)) *
            ((1 + |v|) * Real.exp (-(v ^ 2))) := by
          rw [neg_sq, abs_neg, abs_of_pos (by linarith : 0 < d + η)]
          field_simp [hqpos.ne']
  unfold smoothAFEZetaDisplacedDualWeightAt
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) * ‖∫ v : ℝ, f v‖
      ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, ‖f v‖ := by
        exact mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm f) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
          ∫ v : ℝ, D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply integral_mono_ae hf.norm hmajor
        exact Filter.Eventually.of_forall hpoint
    _ = C * Y ^ (d + η) / (max 1 |τ|) ^ (d + η) := by
      rw [integral_const_mul]
      dsimp only [C, D, G]
      ring

end RHTower
