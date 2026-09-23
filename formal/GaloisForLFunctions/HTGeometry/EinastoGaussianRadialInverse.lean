import GaloisForLFunctions.HTGeometry.EinastoGaussianSource

/-!
# Actual regular radial inverse for the Gaussian Einasto source

Construct the paper's equation (15) from the actual source. Its rescaled
integral is h(r)=r²G(r), with G continuous at the center. Prove the actual first
and second derivatives and their normalized limits; source regularity alone is
not substituted for curvature regularity. The literal appendix integral agrees
with the construction near zero for its printed algebraic sign.
-/
noncomputable section
open Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoGaussianCorrectionFactor (d l σ r : ℝ) : ℝ :=
  8 * Real.pi * ∫ u in (0 : ℝ)..1, u ^ (2 : ℕ) * einastoGaussianSource d l σ (r * u)

def einastoGaussianCorrection (d l σ r : ℝ) : ℝ := r ^ (2 : ℕ) * einastoGaussianCorrectionFactor d l σ r

def einastoGaussianCorrectionCoefficient (d l σ : ℝ) : ℝ := 8 * Real.pi * einastoGaussianSource d l σ 0 / 3

theorem einastoGaussianCorrectionFactor_continuous (d l σ : ℝ) :
    Continuous (einastoGaussianCorrectionFactor d l σ) := by
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_snd.pow 2).mul ((einastoGaussianSource_continuous d l σ).comp
    (continuous_fst.mul continuous_snd))

theorem einastoGaussianCorrectionFactor_core (d l σ : ℝ) :
    einastoGaussianCorrectionFactor d l σ 0 = einastoGaussianCorrectionCoefficient d l σ := by
  simp only [einastoGaussianCorrectionFactor, zero_mul, einastoGaussianCorrectionCoefficient]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num
  ring

/-- The finite quadratic coefficient is extracted from the actual source. -/
theorem einastoGaussianCorrectionCoefficient_eq (d l σ : ℝ) :
    einastoGaussianCorrectionCoefficient d l σ =
      -192 * Real.pi * exp d / exp l ^ (2 : ℕ) + (512 / 3 : ℝ) * Real.pi ^ (2 : ℕ) * (σ - 1) * exp d ^ (2 : ℕ) := by
  rw [einastoGaussianCorrectionCoefficient, einastoGaussianSource_core]
  ring

theorem einastoGaussianCorrection_continuous (d l σ : ℝ) : Continuous (einastoGaussianCorrection d l σ) :=
  (continuous_id.pow 2).mul (einastoGaussianCorrectionFactor_continuous d l σ)

theorem einastoGaussianCorrection_center (d l σ : ℝ) : einastoGaussianCorrection d l σ 0 = 0 := by
  unfold einastoGaussianCorrection
  ring

theorem einastoGaussianCorrection_primitive (d l σ r : ℝ) :
    r * einastoGaussianCorrection d l σ r = ∫ s in 0..r, 8 * Real.pi * s ^ (2 : ℕ) * einastoGaussianSource d l σ s := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun s : ℝ => s ^ (2 : ℕ) * einastoGaussianSource d l σ s) r (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, mul_one, mul_pow] at h
  rw [show (fun u : ℝ => r ^ (2 : ℕ) * u ^ (2 : ℕ) * einastoGaussianSource d l σ (r * u)) =
    (fun u : ℝ => r ^ (2 : ℕ) * (u ^ (2 : ℕ) * einastoGaussianSource d l σ (r * u))) by funext u; ring,
    intervalIntegral.integral_const_mul] at h
  rw [show (fun s : ℝ => 8 * Real.pi * s ^ (2 : ℕ) * einastoGaussianSource d l σ s) =
    (fun s : ℝ => (8 * Real.pi) * (s ^ (2 : ℕ) * einastoGaussianSource d l σ s)) by funext s; ring,
    intervalIntegral.integral_const_mul, ← h]
  unfold einastoGaussianCorrection einastoGaussianCorrectionFactor
  ring

theorem einastoGaussianCorrection_integral (d l σ r : ℝ) :
    einastoGaussianCorrection d l σ r = (∫ s in 0..r, 8 * Real.pi * s ^ (2 : ℕ) * einastoGaussianSource d l σ s) / r := by
  by_cases hr : r = 0
  · subst r
    simp only [einastoGaussianCorrection_center, intervalIntegral.integral_same, zero_div]
  · apply (eq_div_iff hr).mpr
    simpa only [mul_comm] using einastoGaussianCorrection_primitive d l σ r

/-- The constructed correction is equation (15) with the actual curvature source. -/
theorem einastoGaussianCorrection_actual_integral (d l σ t : ℝ) :
    einastoGaussianCorrection d l σ (exp t) =
      (∫ s in 0..exp t, 8 * Real.pi * s ^ (2 : ℕ) * quadraticRadialSource σ (einastoMetric d l einastoGaussianShape) s) / exp t := by
  rw [einastoGaussianCorrection_integral]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (exp_pos t).le
  intro s hs
  have h := einastoGaussianSource_actual d l σ (log s)
  rw [exp_log hs.1] at h
  dsimp only
  rw [h]

/-- The literal printed appendix also gives this regular inverse near zero. -/
theorem einastoGaussianCorrection_appendix_integral (d l : ℝ) :
    (fun t => einastoGaussianCorrection d l (-1) (exp t)) =ᶠ[atBot]
      (fun t => (∫ s in 0..exp t, 8 * Real.pi * s ^ (2 : ℕ) * quadraticAppendixSource (einastoMetric d l einastoGaussianShape) s) / exp t) := by
  obtain ⟨T, hT⟩ := eventually_atBot.mp (einastoGaussianSource_appendix_eventually d l)
  filter_upwards [eventually_le_atBot T] with t ht
  rw [einastoGaussianCorrection_integral]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (exp_pos t).le
  intro s hs
  have hst : log s ≤ t := by
    apply exp_le_exp.mp
    rw [exp_log hs.1]
    exact hs.2.le
  have he := hT (log s) (hst.trans ht)
  dsimp only at he ⊢
  rw [exp_log hs.1] at he
  rw [he]

theorem einastoGaussianCorrection_primitive_hasDerivAt (d l σ r : ℝ) :
    HasDerivAt (fun s => s * einastoGaussianCorrection d l σ s)
      (8 * Real.pi * r ^ (2 : ℕ) * einastoGaussianSource d l σ r) r := by
  have hc : Continuous (fun s : ℝ => 8 * Real.pi * s ^ (2 : ℕ) * einastoGaussianSource d l σ s) :=
    (continuous_const.mul (continuous_id.pow 2)).mul (einastoGaussianSource_continuous d l σ)
  have he : (fun s => s * einastoGaussianCorrection d l σ s) =
      (fun s => ∫ u in 0..s, 8 * Real.pi * u ^ (2 : ℕ) * einastoGaussianSource d l σ u) := by
    funext s
    exact einastoGaussianCorrection_primitive d l σ s
  rw [he]
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem einastoGaussianCorrection_source_ode (d l σ t : ℝ) :
    HasDerivAt (fun r => r * einastoGaussianCorrection d l σ r)
      (8 * Real.pi * exp t ^ (2 : ℕ) * quadraticRadialSource σ (einastoMetric d l einastoGaussianShape) (exp t)) (exp t) := by
  rw [einastoGaussianSource_actual]
  exact einastoGaussianCorrection_primitive_hasDerivAt d l σ (exp t)

theorem einastoGaussianCorrection_hasDerivAt (d l σ t : ℝ) :
    HasDerivAt (einastoGaussianCorrection d l σ)
      (exp t * (8 * Real.pi * einastoGaussianSource d l σ (exp t) - einastoGaussianCorrectionFactor d l σ (exp t))) (exp t) := by
  have h := (einastoGaussianCorrection_primitive_hasDerivAt d l σ (exp t)).div
    (hasDerivAt_id (exp t)) (exp_ne_zero t)
  have he : (fun r => r * einastoGaussianCorrection d l σ r / r) = einastoGaussianCorrection d l σ := by
    funext r
    by_cases hr : r = 0
    · simp [hr, einastoGaussianCorrection_center]
    · field_simp
  simp only [Pi.div_def, id_eq] at h
  rw [he] at h
  apply h.congr_deriv
  unfold einastoGaussianCorrection
  field_simp

/-- Differentiating the exact quotient gives the correction factor's derivative. -/
theorem einastoGaussianCorrectionFactor_hasDerivAt (d l σ t : ℝ) :
    HasDerivAt (einastoGaussianCorrectionFactor d l σ)
      ((8 * Real.pi * einastoGaussianSource d l σ (exp t) - 3 * einastoGaussianCorrectionFactor d l σ (exp t)) / exp t) (exp t) := by
  have h := (einastoGaussianCorrection_hasDerivAt d l σ t).div
    ((hasDerivAt_id (exp t)).pow 2) (pow_ne_zero 2 (exp_ne_zero t))
  simp only [Pi.div_def, Pi.pow_apply, id_eq] at h
  have hd : HasDerivAt (fun r => einastoGaussianCorrection d l σ r / r ^ (2 : ℕ))
      ((8 * Real.pi * einastoGaussianSource d l σ (exp t) - 3 * einastoGaussianCorrectionFactor d l σ (exp t)) / exp t) (exp t) := by
    apply h.congr_deriv
    unfold einastoGaussianCorrection
    norm_num only [Nat.cast_ofNat, pow_one]
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  unfold einastoGaussianCorrection
  field_simp [hr.ne']

/-- The actual second derivative is controlled by the proved source derivative. -/
theorem einastoGaussianCorrection_second_hasDerivAt (d l σ t : ℝ) :
    HasDerivAt (deriv (einastoGaussianCorrection d l σ))
      (2 * einastoGaussianCorrectionFactor d l σ (exp t) +
        8 * Real.pi * exp t * einastoGaussianSourceSlope d l σ (exp t)) (exp t) := by
  have h := (hasDerivAt_id (exp t)).mul
    (((einastoGaussianSource_hasDerivAt d l σ t).const_mul (8 * Real.pi)).sub
      (einastoGaussianCorrectionFactor_hasDerivAt d l σ t))
  simp only [Pi.mul_def, Pi.sub_def, id_eq] at h
  have hd : HasDerivAt (fun r => r * (8 * Real.pi * einastoGaussianSource d l σ r - einastoGaussianCorrectionFactor d l σ r))
      (2 * einastoGaussianCorrectionFactor d l σ (exp t) + 8 * Real.pi * exp t * einastoGaussianSourceSlope d l σ (exp t)) (exp t) := by
    apply h.congr_deriv
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoGaussianCorrection_hasDerivAt d l σ (log r)).deriv
  simpa only [exp_log hr] using he

/-- Quadratic, not linear, leading behavior of the actual metric correction. -/
theorem einastoGaussianCorrection_quadratic_limit (d l σ : ℝ) :
    Tendsto (fun t => einastoGaussianCorrection d l σ (exp t) / exp t ^ (2 : ℕ)) atBot
      (𝓝 (einastoGaussianCorrectionCoefficient d l σ)) := by
  have he : (fun t => einastoGaussianCorrection d l σ (exp t) / exp t ^ (2 : ℕ)) =
      (fun t => einastoGaussianCorrectionFactor d l σ (exp t)) := by
    funext t
    unfold einastoGaussianCorrection
    field_simp
  rw [he, ← einastoGaussianCorrectionFactor_core d l σ]
  exact (einastoGaussianCorrectionFactor_continuous d l σ).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoGaussianCorrection_scaled_derivative_limit (d l σ : ℝ) :
    Tendsto (fun t => deriv (einastoGaussianCorrection d l σ) (exp t) / exp t) atBot
      (𝓝 (2 * einastoGaussianCorrectionCoefficient d l σ)) := by
  have he : (fun t => deriv (einastoGaussianCorrection d l σ) (exp t) / exp t) =
      (fun t => 8 * Real.pi * einastoGaussianSource d l σ (exp t) - einastoGaussianCorrectionFactor d l σ (exp t)) := by
    funext t
    rw [(einastoGaussianCorrection_hasDerivAt d l σ t).deriv]
    field_simp
  rw [he]
  have hS := ((einastoGaussianSource_continuous d l σ).continuousAt.tendsto.comp tendsto_exp_atBot).const_mul (8 * Real.pi)
  have hG := (einastoGaussianCorrectionFactor_continuous d l σ).continuousAt.tendsto.comp tendsto_exp_atBot
  rw [einastoGaussianCorrectionFactor_core] at hG
  have h := hS.sub hG
  simp only [Function.comp_apply] at h
  have hc : 8 * Real.pi * einastoGaussianSource d l σ 0 - einastoGaussianCorrectionCoefficient d l σ =
      2 * einastoGaussianCorrectionCoefficient d l σ := by
    unfold einastoGaussianCorrectionCoefficient
    ring
  rw [hc] at h
  exact h

theorem einastoGaussianCorrection_second_derivative_limit (d l σ : ℝ) :
    Tendsto (fun t => deriv (deriv (einastoGaussianCorrection d l σ)) (exp t)) atBot
      (𝓝 (2 * einastoGaussianCorrectionCoefficient d l σ)) := by
  have he : (fun t => deriv (deriv (einastoGaussianCorrection d l σ)) (exp t)) =
      (fun t => 2 * einastoGaussianCorrectionFactor d l σ (exp t) + 8 * Real.pi * exp t * einastoGaussianSourceSlope d l σ (exp t)) := by
    funext t
    exact (einastoGaussianCorrection_second_hasDerivAt d l σ t).deriv
  rw [he]
  have hG := einastoGaussianCorrectionFactor_continuous d l σ
  have hS := einastoGaussianSourceSlope_continuous d l σ
  have hc : Continuous (fun r : ℝ => 2 * einastoGaussianCorrectionFactor d l σ r + 8 * Real.pi * r * einastoGaussianSourceSlope d l σ r) := by
    fun_prop
  simpa [Function.comp_def, einastoGaussianCorrectionFactor_core] using hc.continuousAt.tendsto.comp tendsto_exp_atBot

end GaloisForLFunctions.HTGeometry
