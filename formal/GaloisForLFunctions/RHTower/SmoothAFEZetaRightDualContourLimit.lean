import GaloisForLFunctions.RHTower.SmoothAFEZetaRightDualContour

/-!
# Infinite right-line dual contour and conductor localization

Gaussian decay sends the horizontal sides of the right-line residue
rectangle to zero.  The remaining negative vertical integral is then
bounded by the direct `T⁻η` chi-ratio estimate.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

theorem norm_smoothAFEZetaRightDualIntegrand_horizontal_le
    {d η Y : ℝ} (hd : 0 < d) (_hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) {u T : ℝ}
    (huLow : -η ≤ u) (huHigh : u ≤ 1)
    (hT : 1 ≤ |T|) (hheight : 256 ≤ |τ - T|) :
    ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
          (-((u : ℂ) + (T : ℂ) * I)) *
        smoothAFEMellinIntegrand Y
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
      ((Real.exp 2 + 1) *
          ‖(zetaChi (rightDisplacedLinePt d τ))⁻¹‖ *
          Real.exp |Real.log Y| * Real.exp 1) *
        ((1 + |τ - T|) ^ 2 * Real.exp (-(T ^ 2))) := by
  have huLower : -1 ≤ u := by linarith
  have hchiNum :
      ‖zetaChi (rightDisplacedLinePt d τ -
          ((u : ℂ) + (T : ℂ) * I))‖ ≤
        (Real.exp 2 + 1) * (1 + |τ - T|) ^ 2 := by
    have harg : rightDisplacedLinePt d τ - ((u : ℂ) + (T : ℂ) * I) =
        (((1 / 2 + d - u : ℝ) : ℂ) + ((τ - T : ℝ) : ℂ) * I) := by
      unfold rightDisplacedLinePt
      push_cast
      ring
    rw [harg]
    by_cases hright : 1 / 2 ≤ 1 / 2 + d - u
    · have hbase := norm_zetaChi_le_one_right_half_strip
        (σ := 1 / 2 + d - u) (t := τ - T)
        hright (by linarith) hheight
      have hsq : 1 ≤ (1 + |τ - T|) ^ 2 := by
        nlinarith [abs_nonneg (τ - T)]
      calc
        ‖zetaChi (↑(1 / 2 + d - u) + ↑(τ - T) * I)‖ ≤ 1 := hbase
        _ ≤ (Real.exp 2 + 1) * (1 + |τ - T|) ^ 2 := by
          have : 1 ≤ Real.exp 2 + 1 := by
            nlinarith [Real.exp_pos 2]
          nlinarith
    · have hbase := norm_zetaChi_le_half_strip
        (σ := 1 / 2 + d - u) (t := τ - T)
        (by linarith) (by linarith) (by linarith)
      have hlin : 1 + |τ - T| ≤ (1 + |τ - T|) ^ 2 := by
        nlinarith [abs_nonneg (τ - T)]
      calc
        ‖zetaChi (↑(1 / 2 + d - u) + ↑(τ - T) * I)‖
            ≤ Real.exp 2 * (1 + |τ - T|) := hbase
        _ ≤ Real.exp 2 * (1 + |τ - T|) ^ 2 := by gcongr
        _ ≤ (Real.exp 2 + 1) * (1 + |τ - T|) ^ 2 := by
          nlinarith [sq_nonneg (1 + |τ - T|)]
  have hratio :
      ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
          (-((u : ℂ) + (T : ℂ) * I))‖ ≤
        ((Real.exp 2 + 1) * (1 + |τ - T|) ^ 2) *
          ‖(zetaChi (rightDisplacedLinePt d τ))⁻¹‖ := by
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
    ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
          (-(↑u + ↑T * I))‖ *
        (‖(Y : ℂ) ^ (-(↑u + ↑T * I))‖ *
          ‖smoothAFEGaussianKernel (↑u + ↑T * I)‖)
      ≤ (((Real.exp 2 + 1) * (1 + |τ - T|) ^ 2) *
          ‖(zetaChi (rightDisplacedLinePt d τ))⁻¹‖) *
        (Real.exp |Real.log Y| *
          (Real.exp 1 * Real.exp (-(T ^ 2)))) := by gcongr
    _ = ((Real.exp 2 + 1) *
          ‖(zetaChi (rightDisplacedLinePt d τ))⁻¹‖ *
          Real.exp |Real.log Y| * Real.exp 1) *
        ((1 + |τ - T|) ^ 2 * Real.exp (-(T ^ 2))) := by ring

theorem tendsto_smoothAFEZetaRightDual_horizontal_top
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-η)..1,
          smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
              (-((u : ℂ) + (T : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ :=
    (Real.exp 2 + 1) *
      ‖(zetaChi (rightDisplacedLinePt d τ))⁻¹‖ *
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
  have hpoint : ∀ u ∈ Set.uIoc (-η) 1,
      ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
            (-((u : ℂ) + (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : -η ≤ (1 : ℝ))] at hu
    have hb := norm_smoothAFEZetaRightDualIntegrand_horizontal_le
      hd hdhalf hη hdηhalf hY τ hu.1.le hu.2
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ T)] using hT1) hheight
    calc
      ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
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
    ‖∫ u : ℝ in (-η)..1,
        smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
            (-((u : ℂ) + (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) + (T : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) *
          |1 - (-η)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ ≤ (2 * B) * (1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2)) := by
      have hlen : |1 - (-η)| ≤ 2 := by
        rw [abs_of_pos (by linarith)]
        linarith
      have hnonneg :
          0 ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
        positivity
      nlinarith

theorem tendsto_smoothAFEZetaRightDual_horizontal_bottom
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-η)..1,
          smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
              (-((u : ℂ) - (T : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ :=
    (Real.exp 2 + 1) *
      ‖(zetaChi (rightDisplacedLinePt d τ))⁻¹‖ *
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
  have hpoint : ∀ u ∈ Set.uIoc (-η) 1,
      ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
            (-((u : ℂ) - (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : -η ≤ (1 : ℝ))] at hu
    have hb := norm_smoothAFEZetaRightDualIntegrand_horizontal_le
      hd hdhalf hη hdηhalf hY τ hu.1.le hu.2
      (T := -T)
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ T)] using hT1)
      (by simpa using hheight)
    have hb' :
        ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
              (-((u : ℂ) - (T : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              ((u : ℂ) - (T : ℂ) * I)‖ ≤
          B * ((1 + |τ + T|) ^ 2 * Real.exp (-(T ^ 2))) := by
      simpa [B, neg_sq, sub_eq_add_neg] using hb
    calc
      ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
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
    ‖∫ u : ℝ in (-η)..1,
        smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
            (-((u : ℂ) - (T : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            ((u : ℂ) - (T : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) *
          |1 - (-η)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ ≤ (2 * B) * (1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2)) := by
      have hlen : |1 - (-η)| ≤ 2 := by
        rw [abs_of_pos (by linarith)]
        linarith
      have hnonneg :
          0 ≤ B * ((1 + |τ| + T) ^ 2 * Real.exp (-(T ^ 2))) := by
        positivity
      nlinarith

theorem tendsto_smoothAFEZetaRightDual_right_intervalIntegral
    {d Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            (((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaRightDualWeightAt_one_integrable hd hdhalf hY τ)
    tendsto_neg_atTop_atBot tendsto_id

theorem tendsto_smoothAFEZetaRightDual_left_intervalIntegral
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
              (-(((-η : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((-η : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
            (-(((-η : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y
            (((-η : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaRightDualWeightAt_neg_integrable
      hd hdhalf hη hdηhalf hY τ)
    tendsto_neg_atTop_atBot tendsto_id

theorem smoothAFEZetaRightDual_infinite_contour
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    I • (∫ v : ℝ,
          smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
      I • (∫ v : ℝ,
          smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
              (-(((-η : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEMellinIntegrand Y
              (((-η : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I := by
  let F : ℂ → ℂ := fun w =>
    smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ) (-w) *
      smoothAFEMellinIntegrand Y w
  have hright := tendsto_smoothAFEZetaRightDual_right_intervalIntegral
    hd hdhalf hY τ
  have hleft := tendsto_smoothAFEZetaRightDual_left_intervalIntegral
    hd hdhalf hη hdηhalf hY τ
  have hbottom := tendsto_smoothAFEZetaRightDual_horizontal_bottom
    hd hdhalf hη hdηhalf hY τ
  have htop := tendsto_smoothAFEZetaRightDual_horizontal_top
    hd hdhalf hη hdηhalf hY τ
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-η)..1,
              F ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (-η)..1,
              F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T,
            F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T,
            F (((-η : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝
        (I • (∫ v : ℝ,
              F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
          I • (∫ v : ℝ,
            F (((-η : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [F, sub_eq_add_neg] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-η)..1,
            F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-η)..1,
            F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T,
          F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T,
          F (((-η : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hfinite := smoothAFEZetaRightDualWeight_finite_contour
      hd hdhalf hη hdηhalf hY hT τ
    simpa [F, RHTower.rectIntegral, sub_eq_add_neg] using hfinite
  have hrhs : Tendsto (fun _T : ℝ => 2 * Real.pi * I)
      atTop (𝓝 (2 * Real.pi * I)) := tendsto_const_nhds
  exact tendsto_nhds_unique (hlimit'.congr' hevent) hrhs

/-- Exact negative-contour representation of the direct right-line weight. -/
theorem smoothAFEZetaRightDualWeight_eq_one_add_at_neg
    {d η Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2)
    (hY : 0 < Y) (τ : ℝ) :
    smoothAFEZetaRightDualWeight d τ Y =
      1 + smoothAFEZetaRightDualWeightAt (-η) d τ Y := by
  let R : ℂ := ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  let L : ℂ := ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
        (-(((-η : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((-η : ℝ) : ℂ) + (v : ℂ) * I)
  have hraw := smoothAFEZetaRightDual_infinite_contour
    hd hdhalf hη hdηhalf hY τ
  have hdiff : R - L = (2 * Real.pi : ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R, L, smul_eq_mul, mul_sub, mul_assoc, mul_left_comm,
      mul_comm] using hraw
  unfold smoothAFEZetaRightDualWeight smoothAFEZetaRightDualWeightAt
    smoothAFEZetaDisplacedDualWeightAt
  rw [displacedLinePt_neg_displacement_eq_right]
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

/-- Direct conductor-localized right-line estimate. -/
theorem exists_norm_smoothAFEZetaRightDualWeight_sub_one_le_conductor
    {d η : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) {Y : ℝ}, 0 < Y →
      ‖smoothAFEZetaRightDualWeight d τ Y - 1‖ ≤
        C * Y ^ η / (max 1 |τ|) ^ η := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_rightDisplaced_le
      hd hdhalf hη hdηhalf
  let G : ℝ :=
    ∫ v : ℝ, (1 + |v|) * Real.exp (-(v ^ 2))
  let C : ℝ :=
    (1 / (2 * Real.pi)) * K *
      (Real.exp (η ^ 2) / η) * G
  have hG : 0 ≤ G := integral_nonneg fun v => by positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun τ {Y} hY => ?_⟩
  have hweight := smoothAFEZetaRightDualWeight_eq_one_add_at_neg
    hd hdhalf hη hdηhalf hY τ
  have hdiff :
      smoothAFEZetaRightDualWeight d τ Y - 1 =
        smoothAFEZetaRightDualWeightAt (-η) d τ Y := by
    rw [hweight]
    ring
  rw [hdiff]
  let f : ℝ → ℂ := fun v =>
    smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
        (-(((-η : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((-η : ℝ) : ℂ) + (v : ℂ) * I)
  let D : ℝ :=
    K * (Y ^ η / (max 1 |τ|) ^ η) *
      (Real.exp (η ^ 2) / η)
  have hf : Integrable f :=
    smoothAFEZetaRightDualWeightAt_neg_integrable
      hd hdhalf hη hdηhalf hY τ
  have hmajor : Integrable (fun v : ℝ =>
      D * ((1 + |v|) * Real.exp (-(v ^ 2)))) :=
    integrable_one_add_abs_mul_exp_neg_sq.const_mul D
  have hpoint : ∀ v : ℝ,
      ‖f v‖ ≤ D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
    intro v
    have hr := hratio τ v
    have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
      (σ := -η) (by linarith) v
    have hpow :
        ‖(Y : ℂ) ^ (-(((-η : ℝ) : ℂ) + (v : ℂ) * I))‖ =
          Y ^ η := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      simp
    have hvbase : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hvpow : (1 + |v|) ^ (d + η) ≤ 1 + |v| := by
      simpa using
        Real.rpow_le_rpow_of_exponent_le hvbase
          (by linarith : d + η ≤ 1)
    have hqpos : 0 < (max 1 |τ|) ^ η :=
      Real.rpow_pos_of_pos
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) η
    dsimp only [f, D]
    unfold smoothAFEMellinIntegrand
    rw [norm_mul, norm_mul, hpow]
    calc
      ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
          (-(((-η : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          (Y ^ η *
            ‖smoothAFEGaussianKernel
              (((-η : ℝ) : ℂ) + (v : ℂ) * I)‖)
        ≤ (K * (1 + |v|) ^ (d + η) / (max 1 |τ|) ^ η) *
            (Y ^ η *
              ((Real.exp ((-η) ^ 2) / |-η|) *
                Real.exp (-(v ^ 2)))) := by
          gcongr
      _ ≤ (K * (1 + |v|) / (max 1 |τ|) ^ η) *
            (Y ^ η *
              ((Real.exp ((-η) ^ 2) / |-η|) *
                Real.exp (-(v ^ 2)))) := by
          gcongr
      _ = K * (Y ^ η / (max 1 |τ|) ^ η) *
            (Real.exp (η ^ 2) / η) *
            ((1 + |v|) * Real.exp (-(v ^ 2))) := by
          rw [neg_sq, abs_neg, abs_of_pos hη]
          field_simp [hqpos.ne']
  unfold smoothAFEZetaRightDualWeightAt
    smoothAFEZetaDisplacedDualWeightAt
  rw [displacedLinePt_neg_displacement_eq_right]
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
    _ = C * Y ^ η / (max 1 |τ|) ^ η := by
      rw [integral_const_mul]
      dsimp only [C, D, G]
      ring

end RHTower
