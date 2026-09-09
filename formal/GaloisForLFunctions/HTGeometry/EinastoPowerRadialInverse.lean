import GaloisForLFunctions.HTGeometry.EinastoShapeEulerDerivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact power-law radial inverse for every positive Einasto shape exponent

The corrected-sign source in arXiv:2608.23600 factors as U(r) N(r)/r²,
where U=(r/η)^q and q>0. Construct its actual integral inverse as U(r) F(r).
The rescaled factor F is continuous and has a nonzero central value for every
shape. Prove actual first and second derivatives and all three normalized
limits needed for a complete curvature classification, without source bounds.
-/
noncomputable section
open Filter Real Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoPowerCorrectionFactor (d l a r : ℝ) : ℝ :=
  8 * Real.pi * ∫ u in (0 : ℝ)..1, u ^ exp (-a) * einastoShapeSourceFactor d l a (r * u)

def einastoPowerCorrection (d l a r : ℝ) : ℝ :=
  einastoProfilePower l a r * einastoPowerCorrectionFactor d l a r

/-- The normalization uses U=(r/η)^q, so η is already included in the radial power. -/
def einastoPowerCorrectionCoefficient (d a : ℝ) : ℝ :=
  -16 * Real.pi * exp (-a) * (exp (-a) + 4) * exp d

theorem einastoPowerCorrectionFactor_continuous (d l a : ℝ) : Continuous (einastoPowerCorrectionFactor d l a) := by
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_rpow_const (exp_pos (-a)).le).comp continuous_snd).mul
    ((einastoShapeSourceFactor_continuous d l a).comp (continuous_fst.mul continuous_snd))

theorem einastoPowerCorrectionFactor_core (d l a : ℝ) :
    einastoPowerCorrectionFactor d l a 0 = einastoPowerCorrectionCoefficient d a := by
  simp only [einastoPowerCorrectionFactor, zero_mul]
  rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (by linarith [exp_pos (-a)]))]
  have hq : exp (-a) + 1 ≠ 0 := by positivity
  simp only [one_rpow, zero_rpow hq, sub_zero]
  rw [einastoShapeSourceFactor_core]
  unfold einastoPowerCorrectionCoefficient
  field_simp
  ring

theorem einastoPowerCorrectionCoefficient_neg (d a : ℝ) : einastoPowerCorrectionCoefficient d a < 0 := by
  unfold einastoPowerCorrectionCoefficient
  have h : 0 < 16 * Real.pi * exp (-a) * (exp (-a) + 4) * exp d := by positivity
  linarith

theorem einastoPowerCorrection_continuous (d l a : ℝ) : Continuous (einastoPowerCorrection d l a) :=
  (einastoProfilePower_continuous l a).mul (einastoPowerCorrectionFactor_continuous d l a)

theorem einastoPowerCorrection_center (d l a : ℝ) : einastoPowerCorrection d l a 0 = 0 := by
  rw [einastoPowerCorrection, einastoProfilePower_zero, zero_mul]

/-- Exact change of variables in the actual radial primitive. -/
theorem einastoPowerCorrection_primitive (d l a t : ℝ) :
    exp t * einastoPowerCorrection d l a (exp t) =
      ∫ v in 0..exp t, 8 * Real.pi * einastoProfilePower l a v * einastoShapeSourceFactor d l a v := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun v : ℝ => einastoProfilePower l a v * einastoShapeSourceFactor d l a v) (exp t) (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, mul_one] at h
  have hi : (∫ u in (0 : ℝ)..1, einastoProfilePower l a (exp t * u) * einastoShapeSourceFactor d l a (exp t * u)) =
      einastoProfilePower l a (exp t) * ∫ u in (0 : ℝ)..1, u ^ exp (-a) * einastoShapeSourceFactor d l a (exp t * u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    dsimp only
    have hp : einastoProfilePower l a (exp t * u) = einastoProfilePower l a (exp t) * u ^ exp (-a) := by
      unfold einastoProfilePower
      rw [show exp t * u / exp l = (exp t / exp l) * u by ring,
        mul_rpow (by positivity : 0 ≤ exp t / exp l) hu.1.le]
    rw [hp]
    ring
  rw [hi] at h
  rw [show (fun v : ℝ => 8 * Real.pi * einastoProfilePower l a v * einastoShapeSourceFactor d l a v) =
      (fun v : ℝ => (8 * Real.pi) * (einastoProfilePower l a v * einastoShapeSourceFactor d l a v)) by funext v; ring,
    intervalIntegral.integral_const_mul, ← h]
  unfold einastoPowerCorrection einastoPowerCorrectionFactor
  ring

theorem einastoPowerCorrection_integral (d l a t : ℝ) :
    einastoPowerCorrection d l a (exp t) =
      (∫ v in 0..exp t, 8 * Real.pi * einastoProfilePower l a v * einastoShapeSourceFactor d l a v) / exp t := by
  apply (eq_div_iff (exp_ne_zero t)).mpr
  simpa only [mul_comm] using einastoPowerCorrection_primitive d l a t

/-- Equation (15) with the actual corrected-sign source, for every positive shape exponent. -/
theorem einastoPowerCorrection_actual_integral (d l a t : ℝ) :
    einastoPowerCorrection d l a (exp t) =
      (∫ v in 0..exp t, 8 * Real.pi * v ^ 2 * quadraticRadialSource 1 (einastoMetric d l a) v) / exp t := by
  rw [einastoPowerCorrection_integral]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (exp_pos t).le
  intro v hv
  have h := einastoShapeSource_decomposition d l a 1 (log v)
  rw [exp_log hv.1] at h
  dsimp only
  rw [h]
  simp only [einastoShapeSourceDefect, sub_self, zero_mul, zero_div, add_zero]
  field_simp [hv.1.ne']

theorem einastoPowerCorrection_primitive_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (fun r => r * einastoPowerCorrection d l a r)
      (8 * Real.pi * einastoProfilePower l a (exp t) * einastoShapeSourceFactor d l a (exp t)) (exp t) := by
  have hc : Continuous (fun v : ℝ => 8 * Real.pi * einastoProfilePower l a v * einastoShapeSourceFactor d l a v) :=
    (continuous_const.mul (einastoProfilePower_continuous l a)).mul (einastoShapeSourceFactor_continuous d l a)
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 (exp t))
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := einastoPowerCorrection_primitive d l a (log r)
  simpa only [exp_log hr] using he

/-- The first derivative is obtained from the actual primitive, not an assumed asymptotic ansatz. -/
theorem einastoPowerCorrection_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (einastoPowerCorrection d l a)
      (einastoProfilePower l a (exp t) / exp t *
        (8 * Real.pi * einastoShapeSourceFactor d l a (exp t) - einastoPowerCorrectionFactor d l a (exp t))) (exp t) := by
  have h := (einastoPowerCorrection_primitive_hasDerivAt d l a t).div
    (hasDerivAt_id (exp t)) (exp_ne_zero t)
  simp only [Pi.div_def, id_eq] at h
  have hd : HasDerivAt (fun r => r * einastoPowerCorrection d l a r / r)
      (einastoProfilePower l a (exp t) / exp t *
        (8 * Real.pi * einastoShapeSourceFactor d l a (exp t) - einastoPowerCorrectionFactor d l a (exp t))) (exp t) := by
    apply h.congr_deriv
    unfold einastoPowerCorrection
    field_simp
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  field_simp [hr.ne']

theorem einastoPowerCorrectionFactor_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (einastoPowerCorrectionFactor d l a)
      ((8 * Real.pi * einastoShapeSourceFactor d l a (exp t) -
        (exp (-a) + 1) * einastoPowerCorrectionFactor d l a (exp t)) / exp t) (exp t) := by
  have hU := einastoProfilePower_hasDerivAt l a t
  have h := (einastoPowerCorrection_hasDerivAt d l a t).div hU (einastoProfilePower_pos l a t).ne'
  simp only [Pi.div_def] at h
  have hd : HasDerivAt (fun r => einastoPowerCorrection d l a r / einastoProfilePower l a r)
      ((8 * Real.pi * einastoShapeSourceFactor d l a (exp t) -
        (exp (-a) + 1) * einastoPowerCorrectionFactor d l a (exp t)) / exp t) (exp t) := by
    apply h.congr_deriv
    unfold einastoPowerCorrection
    field_simp [(einastoProfilePower_pos l a t).ne']
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have hu := einastoProfilePower_pos l a (log r)
  rw [exp_log hr] at hu
  unfold einastoPowerCorrection
  field_simp [hu.ne']

/-- Both power-law derivative factors are exact derivatives of the constructed inverse. -/
theorem einastoPowerCorrection_second_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (deriv (einastoPowerCorrection d l a))
      (einastoProfilePower l a (exp t) / exp t ^ 2 *
        (8 * Real.pi * (exp (-a) - 2) * einastoShapeSourceFactor d l a (exp t) +
          8 * Real.pi * einastoShapeSourceFactorEuler d l a (exp t) + 2 * einastoPowerCorrectionFactor d l a (exp t))) (exp t) := by
  have h := ((einastoProfilePower_hasDerivAt l a t).div (hasDerivAt_id (exp t)) (exp_ne_zero t)).mul
    (((einastoShapeSourceFactor_hasDerivAt d l a t).const_mul (8 * Real.pi)).sub
      (einastoPowerCorrectionFactor_hasDerivAt d l a t))
  simp only [Pi.div_def, Pi.mul_def, Pi.sub_def, id_eq] at h
  have hd : HasDerivAt (fun r => einastoProfilePower l a r / r *
      (8 * Real.pi * einastoShapeSourceFactor d l a r - einastoPowerCorrectionFactor d l a r))
      (einastoProfilePower l a (exp t) / exp t ^ 2 *
        (8 * Real.pi * (exp (-a) - 2) * einastoShapeSourceFactor d l a (exp t) +
          8 * Real.pi * einastoShapeSourceFactorEuler d l a (exp t) + 2 * einastoPowerCorrectionFactor d l a (exp t))) (exp t) := by
    apply h.congr_deriv
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoPowerCorrection_hasDerivAt d l a (log r)).deriv
  simpa only [exp_log hr] using he

/-- The inverse retains a nonzero leading radial power for every shape. -/
theorem einastoPowerCorrection_normalized_limit (d l a : ℝ) :
    Tendsto (fun t => einastoPowerCorrection d l a (exp t) / einastoProfilePower l a (exp t)) atBot
      (𝓝 (einastoPowerCorrectionCoefficient d a)) := by
  have he : (fun t => einastoPowerCorrection d l a (exp t) / einastoProfilePower l a (exp t)) =
      (fun t => einastoPowerCorrectionFactor d l a (exp t)) := by
    funext t
    unfold einastoPowerCorrection
    field_simp [(einastoProfilePower_pos l a t).ne']
  rw [he, ← einastoPowerCorrectionFactor_core d l a]
  exact (einastoPowerCorrectionFactor_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoPowerCorrection_scaled_derivative_limit (d l a : ℝ) :
    Tendsto (fun t => exp t * deriv (einastoPowerCorrection d l a) (exp t) / einastoProfilePower l a (exp t)) atBot
      (𝓝 (exp (-a) * einastoPowerCorrectionCoefficient d a)) := by
  have he : (fun t => exp t * deriv (einastoPowerCorrection d l a) (exp t) / einastoProfilePower l a (exp t)) =
      (fun t => 8 * Real.pi * einastoShapeSourceFactor d l a (exp t) - einastoPowerCorrectionFactor d l a (exp t)) := by
    funext t
    rw [(einastoPowerCorrection_hasDerivAt d l a t).deriv]
    field_simp [(einastoProfilePower_pos l a t).ne']
  rw [he]
  have hc : Continuous (fun r => 8 * Real.pi * einastoShapeSourceFactor d l a r - einastoPowerCorrectionFactor d l a r) :=
    (continuous_const.mul (einastoShapeSourceFactor_continuous d l a)).sub (einastoPowerCorrectionFactor_continuous d l a)
  have h := hc.continuousAt.tendsto.comp tendsto_exp_atBot
  have h0 : 8 * Real.pi * einastoShapeSourceFactor d l a 0 - einastoPowerCorrectionFactor d l a 0 =
      exp (-a) * einastoPowerCorrectionCoefficient d a := by
    rw [einastoShapeSourceFactor_core, einastoPowerCorrectionFactor_core]
    unfold einastoPowerCorrectionCoefficient
    ring
  simpa only [Function.comp_def, h0] using h

theorem einastoPowerCorrection_scaled_second_derivative_limit (d l a : ℝ) :
    Tendsto (fun t => exp t ^ 2 * deriv (deriv (einastoPowerCorrection d l a)) (exp t) / einastoProfilePower l a (exp t)) atBot
      (𝓝 (exp (-a) * (exp (-a) - 1) * einastoPowerCorrectionCoefficient d a)) := by
  have he : (fun t => exp t ^ 2 * deriv (deriv (einastoPowerCorrection d l a)) (exp t) / einastoProfilePower l a (exp t)) =
      (fun t => 8 * Real.pi * (exp (-a) - 2) * einastoShapeSourceFactor d l a (exp t) +
        8 * Real.pi * einastoShapeSourceFactorEuler d l a (exp t) + 2 * einastoPowerCorrectionFactor d l a (exp t)) := by
    funext t
    rw [(einastoPowerCorrection_second_hasDerivAt d l a t).deriv]
    field_simp [(einastoProfilePower_pos l a t).ne']
  rw [he]
  have hN := einastoShapeSourceFactor_continuous d l a
  have hJ := einastoShapeSourceFactorEuler_continuous d l a
  have hF := einastoPowerCorrectionFactor_continuous d l a
  have hc : Continuous (fun r => 8 * Real.pi * (exp (-a) - 2) * einastoShapeSourceFactor d l a r +
      8 * Real.pi * einastoShapeSourceFactorEuler d l a r + 2 * einastoPowerCorrectionFactor d l a r) := by fun_prop
  have h := hc.continuousAt.tendsto.comp tendsto_exp_atBot
  have h0 : 8 * Real.pi * (exp (-a) - 2) * einastoShapeSourceFactor d l a 0 +
      8 * Real.pi * einastoShapeSourceFactorEuler d l a 0 + 2 * einastoPowerCorrectionFactor d l a 0 =
      exp (-a) * (exp (-a) - 1) * einastoPowerCorrectionCoefficient d a := by
    rw [einastoShapeSourceFactor_core, einastoShapeSourceFactorEuler_core, einastoPowerCorrectionFactor_core]
    unfold einastoPowerCorrectionCoefficient
    ring
  simpa only [Function.comp_def, h0] using h

end GaloisForLFunctions.HTGeometry
