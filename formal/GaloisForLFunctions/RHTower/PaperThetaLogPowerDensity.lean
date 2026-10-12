import GaloisForLFunctions.RHTower.PaperThetaLogCusp
import GaloisForLFunctions.RHTower.PaperThetaEntireTails

/-! # Sharp logarithmic powers in the original theta source coordinate -/

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics
open scoped NNReal

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

def logPowerDensity (z : ℂ) (a : ℝ≥0) (x : ℝ) : ℝ :=
  ‖flatMode z x‖ * Real.log (2 + ‖flatMode z x‖ / thetaSource.normalized x) ^ (a : ℝ)

theorem mode_log_nonneg (z : ℂ) (x : ℝ) :
    0 ≤ Real.log (2 + ‖flatMode z x‖ / thetaSource.normalized x) := by
  apply Real.log_nonneg
  have := div_nonneg (norm_nonneg (flatMode z x)) (thetaSource.normalized_pos x).le
  linarith

theorem logPowerDensity_nonneg (z : ℂ) (a : ℝ≥0) (x : ℝ) :
    0 ≤ logPowerDensity z a x :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (mode_log_nonneg z x) _)

theorem continuous_logPowerDensity (z : ℂ) (a : ℝ≥0) : Continuous (logPowerDensity z a) := by
  have hu := (continuous_flatMode_all z).norm
  have hl := (continuous_const.add
    (hu.div continuous_normalized_theta fun x => (thetaSource.normalized_pos x).ne')).log
      (fun x => by
        change 2 + ‖flatMode z x‖ / thetaSource.normalized x ≠ 0
        have := thetaSource.normalized_pos x
        positivity)
  exact hu.mul (hl.rpow_const fun _ => Or.inr a.coe_nonneg)

/-- The precise left-tail coefficient, including the critical exponent. -/
theorem tendsto_scaled_logPowerDensity {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0) (a : ℝ≥0) :
    Tendsto (fun x : ℝ => Real.exp ((2 * (a : ℝ) - z.im) * x) * logPowerDensity z a x)
      atBot (𝓝 (‖z‖ * ‖flatConnection z‖ * Real.pi ^ (a : ℝ))) := by
  have h := (tendsto_scaled_flatMode_norm z).mul
    ((tendsto_scaled_mode_log hz hXi).rpow_const (Or.inr a.coe_nonneg))
  refine h.congr fun x => ?_
  rw [Real.mul_rpow (Real.exp_nonneg _) (mode_log_nonneg z x), ← Real.exp_mul]
  have he : Real.exp (-z.im * x) * Real.exp ((2 * x) * (a : ℝ)) =
      Real.exp ((2 * (a : ℝ) - z.im) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [logPowerDensity]
  calc
    _ = (Real.exp (-z.im * x) * Real.exp ((2 * x) * (a : ℝ))) *
        (‖flatMode z x‖ * Real.log (2 + ‖flatMode z x‖ / thetaSource.normalized x) ^ (a : ℝ)) := by ring
    _ = _ := by rw [he]

private theorem normalized_tendsto_zero_atTop :
    Tendsto thetaSource.normalized atTop (𝓝 0) := by
  have h := (tendsto_normalized_mul_exp_atBot_all 0).comp tendsto_neg_atTop_atBot
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, neg_zero, zero_mul, Real.exp_zero, mul_one,
    PositiveDensitySource.normalized, thetaSource_even]

private theorem scaled_log_constant_quotient {B : ℝ} (hB : 0 < B) :
    Tendsto (fun x : ℝ => Real.exp (-2 * x) *
      Real.log (2 + B / thetaSource.normalized x)) atTop (𝓝 Real.pi) := by
  have hnum := (tendsto_const_nhds (x := B)).add (normalized_tendsto_zero_atTop.const_mul 2)
  simp only [mul_zero, add_zero] at hnum
  have h := (tendsto_exp_neg_two_mul.mul (hnum.log hB.ne')).sub
    tendsto_scaled_log_normalized_atTop
  simp only [zero_mul, zero_sub, neg_neg] at h
  refine h.congr fun x => ?_
  have hρ := thetaSource.normalized_pos x
  rw [← mul_sub, ← Real.log_div (by positivity) hρ.ne']
  congr 2
  field_simp
  ring

theorem eventually_mode_log_le_right (z : ℂ) :
    ∀ᶠ x : ℝ in atTop, Real.log (2 + ‖flatMode z x‖ / thetaSource.normalized x) ≤
      (Real.pi + 1) * Real.exp (2 * x) := by
  let B := ‖z‖ * exponentialEnvelopeConstant (|z.im| + 1) + exponentialEnvelopeConstant 0
  have hB : 0 < B := by
    have h0 := exponentialEnvelopeConstant_pos 0
    have h1 := exponentialEnvelopeConstant_pos (|z.im| + 1)
    dsimp [B]
    positivity
  have hev := (scaled_log_constant_quotient hB).eventually (gt_mem_nhds (lt_add_one Real.pi))
  filter_upwards [eventually_ge_atTop (0 : ℝ), hev] with x hx hscaled
  have hu : ‖flatMode z x‖ ≤ B := by
    simpa only [NNReal.coe_zero, zero_add, neg_zero, zero_mul, Real.exp_zero, mul_one, B]
      using norm_flatMode_le_right z 0 hx
  have hρ := thetaSource.normalized_pos x
  have he : Real.exp (2 * x) * Real.exp (-2 * x) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    _ ≤ Real.log (2 + B / thetaSource.normalized x) :=
      Real.log_le_log (by positivity) (by gcongr)
    _ = Real.exp (2 * x) * (Real.exp (-2 * x) * Real.log (2 + B / thetaSource.normalized x)) := by
      rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp (2 * x) * (Real.pi + 1) :=
      mul_le_mul_of_nonneg_left hscaled.le (Real.exp_nonneg _)
    _ = _ := by ring

/-- Every finite logarithmic power is integrable at the right cusp, for every parameter. -/
theorem logPowerDensity_isBigO_right (z : ℂ) (a : ℝ≥0) :
    logPowerDensity z a =O[atTop] (fun x : ℝ => Real.exp (-x)) := by
  let b : ℝ≥0 := ⟨2 * (a : ℝ) + 1, by positivity⟩
  let K := ‖z‖ * exponentialEnvelopeConstant (b + |z.im| + 1) + exponentialEnvelopeConstant b
  have hK : 0 ≤ K := by
    have := exponentialEnvelopeConstant_pos (b + |z.im| + 1)
    have := exponentialEnvelopeConstant_pos b
    dsimp [K]
    positivity
  refine isBigO_iff.mpr ⟨K * (Real.pi + 1) ^ (a : ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_mode_log_le_right z] with x hx hl
  rw [Real.norm_eq_abs, abs_of_nonneg (logPowerDensity_nonneg z a x),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hu := norm_flatMode_le_right z b hx
  have hp := Real.rpow_le_rpow (mode_log_nonneg z x) hl a.coe_nonneg
  calc
    logPowerDensity z a x ≤ (K * Real.exp (-(b : ℝ) * x)) *
        (((Real.pi + 1) * Real.exp (2 * x)) ^ (a : ℝ)) :=
      mul_le_mul hu hp (Real.rpow_nonneg (mode_log_nonneg z x) _)
        (mul_nonneg hK (Real.exp_nonneg _))
    _ = K * (Real.pi + 1) ^ (a : ℝ) * Real.exp (-x) := by
      rw [Real.mul_rpow (by positivity) (Real.exp_nonneg _), ← Real.exp_mul]
      have he : Real.exp (-(b : ℝ) * x) * Real.exp ((2 * x) * (a : ℝ)) = Real.exp (-x) := by
        rw [← Real.exp_add]
        congr 1
        change -(2 * (a : ℝ) + 1) * x + (2 * x) * (a : ℝ) = -x
        ring
      calc
        _ = K * (Real.pi + 1) ^ (a : ℝ) *
            (Real.exp (-(b : ℝ) * x) * Real.exp ((2 * x) * (a : ℝ))) := by ring
        _ = _ := by rw [he]

end RHTower.PaperThetaEndpoint
