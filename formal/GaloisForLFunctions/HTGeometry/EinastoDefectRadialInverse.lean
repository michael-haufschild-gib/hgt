import GaloisForLFunctions.HTGeometry.EinastoShapeEulerDerivative

/-!
# Exact radial inverse of the bounded algebraic source defect

The sign discrepancy in arXiv:2608.23600 contributes a continuous source A
for every Einasto shape. Construct its exact integral inverse r²G(r), prove
actual first and second derivatives, and extract their quadratic limits.
The Euler derivative r A'(r) supplies the second derivative without any
assumption that A' itself is bounded at the center.
-/
noncomputable section
open Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoDefectCorrectionFactor (d l a σ r : ℝ) : ℝ :=
  8 * Real.pi * ∫ u in (0 : ℝ)..1, u ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ (r * u)

def einastoDefectCorrection (d l a σ r : ℝ) : ℝ := r ^ (2 : ℕ) * einastoDefectCorrectionFactor d l a σ r

def einastoDefectCorrectionCoefficient (d l a σ : ℝ) : ℝ := 8 * Real.pi * einastoShapeSourceDefect d l a σ 0 / 3

theorem einastoDefectCorrectionFactor_continuous (d l a σ : ℝ) :
    Continuous (einastoDefectCorrectionFactor d l a σ) := by
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_snd.pow 2).mul ((einastoShapeSourceDefect_continuous d l a σ).comp
    (continuous_fst.mul continuous_snd))

theorem einastoDefectCorrectionFactor_core (d l a σ : ℝ) :
    einastoDefectCorrectionFactor d l a σ 0 = einastoDefectCorrectionCoefficient d l a σ := by
  simp only [einastoDefectCorrectionFactor, zero_mul, einastoDefectCorrectionCoefficient]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num
  ring

/-- The finite quadratic coefficient is extracted from the actual source. -/
theorem einastoDefectCorrectionCoefficient_eq (d l a σ : ℝ) :
    einastoDefectCorrectionCoefficient d l a σ =
      (512 / 3 : ℝ) * Real.pi ^ (2 : ℕ) * (σ - 1) * exp d ^ (2 : ℕ) := by
  rw [einastoDefectCorrectionCoefficient, einastoShapeSourceDefect_core]
  ring

theorem einastoDefectCorrection_continuous (d l a σ : ℝ) : Continuous (einastoDefectCorrection d l a σ) :=
  (continuous_id.pow 2).mul (einastoDefectCorrectionFactor_continuous d l a σ)

theorem einastoDefectCorrection_center (d l a σ : ℝ) : einastoDefectCorrection d l a σ 0 = 0 := by
  unfold einastoDefectCorrection
  ring

theorem einastoDefectCorrection_primitive (d l a σ r : ℝ) :
    r * einastoDefectCorrection d l a σ r = ∫ s in 0..r, 8 * Real.pi * s ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ s := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun s : ℝ => s ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ s) r (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, mul_one, mul_pow] at h
  rw [show (fun u : ℝ => r ^ (2 : ℕ) * u ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ (r * u)) =
    (fun u : ℝ => r ^ (2 : ℕ) * (u ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ (r * u))) by funext u; ring,
    intervalIntegral.integral_const_mul] at h
  rw [show (fun s : ℝ => 8 * Real.pi * s ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ s) =
    (fun s : ℝ => (8 * Real.pi) * (s ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ s)) by funext s; ring,
    intervalIntegral.integral_const_mul, ← h]
  unfold einastoDefectCorrection einastoDefectCorrectionFactor
  ring

theorem einastoDefectCorrection_integral (d l a σ r : ℝ) :
    einastoDefectCorrection d l a σ r = (∫ s in 0..r, 8 * Real.pi * s ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ s) / r := by
  by_cases hr : r = 0
  · subst r
    simp only [einastoDefectCorrection_center, intervalIntegral.integral_same, zero_div]
  · apply (eq_div_iff hr).mpr
    simpa only [mul_comm] using einastoDefectCorrection_primitive d l a σ r

theorem einastoDefectCorrection_primitive_hasDerivAt (d l a σ r : ℝ) :
    HasDerivAt (fun s => s * einastoDefectCorrection d l a σ s)
      (8 * Real.pi * r ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ r) r := by
  have hc : Continuous (fun s : ℝ => 8 * Real.pi * s ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ s) :=
    (continuous_const.mul (continuous_id.pow 2)).mul (einastoShapeSourceDefect_continuous d l a σ)
  have he : (fun s => s * einastoDefectCorrection d l a σ s) =
      (fun s => ∫ u in 0..s, 8 * Real.pi * u ^ (2 : ℕ) * einastoShapeSourceDefect d l a σ u) := by
    funext s
    exact einastoDefectCorrection_primitive d l a σ s
  rw [he]
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem einastoDefectCorrection_hasDerivAt (d l a σ t : ℝ) :
    HasDerivAt (einastoDefectCorrection d l a σ)
      (exp t * (8 * Real.pi * einastoShapeSourceDefect d l a σ (exp t) - einastoDefectCorrectionFactor d l a σ (exp t))) (exp t) := by
  have h := (einastoDefectCorrection_primitive_hasDerivAt d l a σ (exp t)).div
    (hasDerivAt_id (exp t)) (exp_ne_zero t)
  have he : (fun r => r * einastoDefectCorrection d l a σ r / r) = einastoDefectCorrection d l a σ := by
    funext r
    by_cases hr : r = 0
    · simp [hr, einastoDefectCorrection_center]
    · field_simp
  simp only [Pi.div_def, id_eq] at h
  rw [he] at h
  apply h.congr_deriv
  unfold einastoDefectCorrection
  field_simp

/-- Differentiating the exact quotient gives the correction factor's derivative. -/
theorem einastoDefectCorrectionFactor_hasDerivAt (d l a σ t : ℝ) :
    HasDerivAt (einastoDefectCorrectionFactor d l a σ)
      ((8 * Real.pi * einastoShapeSourceDefect d l a σ (exp t) - 3 * einastoDefectCorrectionFactor d l a σ (exp t)) / exp t) (exp t) := by
  have h := (einastoDefectCorrection_hasDerivAt d l a σ t).div
    ((hasDerivAt_id (exp t)).pow 2) (pow_ne_zero 2 (exp_ne_zero t))
  simp only [Pi.div_def, Pi.pow_apply, id_eq] at h
  have hd : HasDerivAt (fun r => einastoDefectCorrection d l a σ r / r ^ (2 : ℕ))
      ((8 * Real.pi * einastoShapeSourceDefect d l a σ (exp t) - 3 * einastoDefectCorrectionFactor d l a σ (exp t)) / exp t) (exp t) := by
    apply h.congr_deriv
    unfold einastoDefectCorrection
    norm_num only [Nat.cast_ofNat, pow_one]
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  unfold einastoDefectCorrection
  field_simp [hr.ne']

/-- The actual second derivative is controlled by the proved source derivative. -/
theorem einastoDefectCorrection_second_hasDerivAt (d l a σ t : ℝ) :
    HasDerivAt (deriv (einastoDefectCorrection d l a σ))
      (2 * einastoDefectCorrectionFactor d l a σ (exp t) +
        8 * Real.pi * einastoShapeSourceDefectEuler d l a σ (exp t)) (exp t) := by
  have h := (hasDerivAt_id (exp t)).mul
    (((einastoShapeSourceDefect_hasDerivAt d l a σ t).const_mul (8 * Real.pi)).sub
      (einastoDefectCorrectionFactor_hasDerivAt d l a σ t))
  simp only [Pi.mul_def, Pi.sub_def, id_eq] at h
  have hd : HasDerivAt (fun r => r * (8 * Real.pi * einastoShapeSourceDefect d l a σ r - einastoDefectCorrectionFactor d l a σ r))
      (2 * einastoDefectCorrectionFactor d l a σ (exp t) + 8 * Real.pi * einastoShapeSourceDefectEuler d l a σ (exp t)) (exp t) := by
    apply h.congr_deriv
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoDefectCorrection_hasDerivAt d l a σ (log r)).deriv
  simpa only [exp_log hr] using he

/-- The algebraic defect always contributes a finite quadratic metric coefficient. -/
theorem einastoDefectCorrection_quadratic_limit (d l a σ : ℝ) :
    Tendsto (fun t => einastoDefectCorrection d l a σ (exp t) / exp t ^ (2 : ℕ)) atBot
      (𝓝 (einastoDefectCorrectionCoefficient d l a σ)) := by
  have he : (fun t => einastoDefectCorrection d l a σ (exp t) / exp t ^ (2 : ℕ)) =
      (fun t => einastoDefectCorrectionFactor d l a σ (exp t)) := by
    funext t
    unfold einastoDefectCorrection
    field_simp
  rw [he, ← einastoDefectCorrectionFactor_core d l a σ]
  exact (einastoDefectCorrectionFactor_continuous d l a σ).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoDefectCorrection_scaled_derivative_limit (d l a σ : ℝ) :
    Tendsto (fun t => deriv (einastoDefectCorrection d l a σ) (exp t) / exp t) atBot
      (𝓝 (2 * einastoDefectCorrectionCoefficient d l a σ)) := by
  have he : (fun t => deriv (einastoDefectCorrection d l a σ) (exp t) / exp t) =
      (fun t => 8 * Real.pi * einastoShapeSourceDefect d l a σ (exp t) - einastoDefectCorrectionFactor d l a σ (exp t)) := by
    funext t
    rw [(einastoDefectCorrection_hasDerivAt d l a σ t).deriv]
    field_simp
  rw [he]
  have hS := ((einastoShapeSourceDefect_continuous d l a σ).continuousAt.tendsto.comp tendsto_exp_atBot).const_mul (8 * Real.pi)
  have hG := (einastoDefectCorrectionFactor_continuous d l a σ).continuousAt.tendsto.comp tendsto_exp_atBot
  rw [einastoDefectCorrectionFactor_core] at hG
  have h := hS.sub hG
  simp only [Function.comp_apply] at h
  have hc : 8 * Real.pi * einastoShapeSourceDefect d l a σ 0 - einastoDefectCorrectionCoefficient d l a σ =
      2 * einastoDefectCorrectionCoefficient d l a σ := by
    unfold einastoDefectCorrectionCoefficient
    ring
  rw [hc] at h
  exact h

theorem einastoDefectCorrection_second_derivative_limit (d l a σ : ℝ) :
    Tendsto (fun t => deriv (deriv (einastoDefectCorrection d l a σ)) (exp t)) atBot
      (𝓝 (2 * einastoDefectCorrectionCoefficient d l a σ)) := by
  have he : (fun t => deriv (deriv (einastoDefectCorrection d l a σ)) (exp t)) =
      (fun t => 2 * einastoDefectCorrectionFactor d l a σ (exp t) + 8 * Real.pi * einastoShapeSourceDefectEuler d l a σ (exp t)) := by
    funext t
    exact (einastoDefectCorrection_second_hasDerivAt d l a σ t).deriv
  rw [he]
  have hG := einastoDefectCorrectionFactor_continuous d l a σ
  have hS := einastoShapeSourceDefectEuler_continuous d l a σ
  have hc : Continuous (fun r : ℝ => 2 * einastoDefectCorrectionFactor d l a σ r + 8 * Real.pi * einastoShapeSourceDefectEuler d l a σ r) := by
    fun_prop
  simpa [Function.comp_def, einastoDefectCorrectionFactor_core, einastoShapeSourceDefectEuler_core] using hc.continuousAt.tendsto.comp tendsto_exp_atBot

/-- The corrected algebraic sign has no defect correction at any radius. -/
theorem einastoDefectCorrection_corrected_sign (d l a r : ℝ) : einastoDefectCorrection d l a 1 r = 0 := by
  simp [einastoDefectCorrection, einastoDefectCorrectionFactor, einastoShapeSourceDefect]

end GaloisForLFunctions.HTGeometry
