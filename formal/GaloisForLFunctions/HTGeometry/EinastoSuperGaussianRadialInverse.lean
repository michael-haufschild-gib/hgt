import GaloisForLFunctions.HTGeometry.EinastoSuperGaussianSource

/-!
# Actual regular radial inverse for every super-Gaussian Einasto source

Apply equation (15) of arXiv:2608.23600 to the actual source for q>2.
The rescaled integral has h(r)=r²G(r). Its actual second derivative is
2G(r)+8πrE'(r), and the weighted derivative is proved to vanish even when
E' itself need not remain bounded. No central derivative bounds are assumed.
The literal appendix integral agrees near zero for its printed sign.
-/
noncomputable section
open Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoSuperGaussianCorrectionFactor (d l k σ r : ℝ) : ℝ :=
  8 * Real.pi * ∫ u in (0 : ℝ)..1, u ^ 2 * einastoSuperGaussianSource d l k σ (r * u)

def einastoSuperGaussianCorrection (d l k σ r : ℝ) : ℝ := r ^ 2 * einastoSuperGaussianCorrectionFactor d l k σ r

def einastoSuperGaussianCorrectionCoefficient (d l k σ : ℝ) : ℝ := 8 * Real.pi * einastoSuperGaussianSource d l k σ 0 / 3

theorem einastoSuperGaussianCorrectionFactor_continuous (d l k σ : ℝ) :
    Continuous (einastoSuperGaussianCorrectionFactor d l k σ) := by
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_snd.pow 2).mul ((einastoSuperGaussianSource_continuous d l k σ).comp
    (continuous_fst.mul continuous_snd))

theorem einastoSuperGaussianCorrectionFactor_core (d l k σ : ℝ) :
    einastoSuperGaussianCorrectionFactor d l k σ 0 = einastoSuperGaussianCorrectionCoefficient d l k σ := by
  simp only [einastoSuperGaussianCorrectionFactor, zero_mul, einastoSuperGaussianCorrectionCoefficient]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num
  ring

/-- The finite quadratic coefficient is extracted from the actual source. -/
theorem einastoSuperGaussianCorrectionCoefficient_eq (d l k σ : ℝ) :
    einastoSuperGaussianCorrectionCoefficient d l k σ =
      (512 / 3 : ℝ) * Real.pi ^ 2 * (σ - 1) * exp d ^ 2 := by
  rw [einastoSuperGaussianCorrectionCoefficient, einastoSuperGaussianSource_core]
  ring

theorem einastoSuperGaussianCorrection_continuous (d l k σ : ℝ) : Continuous (einastoSuperGaussianCorrection d l k σ) :=
  (continuous_id.pow 2).mul (einastoSuperGaussianCorrectionFactor_continuous d l k σ)

theorem einastoSuperGaussianCorrection_center (d l k σ : ℝ) : einastoSuperGaussianCorrection d l k σ 0 = 0 := by
  unfold einastoSuperGaussianCorrection
  ring

theorem einastoSuperGaussianCorrection_primitive (d l k σ r : ℝ) :
    r * einastoSuperGaussianCorrection d l k σ r = ∫ s in 0..r, 8 * Real.pi * s ^ 2 * einastoSuperGaussianSource d l k σ s := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun s : ℝ => s ^ 2 * einastoSuperGaussianSource d l k σ s) r (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, mul_one, mul_pow] at h
  rw [show (fun u : ℝ => r ^ 2 * u ^ 2 * einastoSuperGaussianSource d l k σ (r * u)) =
    (fun u : ℝ => r ^ 2 * (u ^ 2 * einastoSuperGaussianSource d l k σ (r * u))) by funext u; ring,
    intervalIntegral.integral_const_mul] at h
  rw [show (fun s : ℝ => 8 * Real.pi * s ^ 2 * einastoSuperGaussianSource d l k σ s) =
    (fun s : ℝ => (8 * Real.pi) * (s ^ 2 * einastoSuperGaussianSource d l k σ s)) by funext s; ring,
    intervalIntegral.integral_const_mul, ← h]
  unfold einastoSuperGaussianCorrection einastoSuperGaussianCorrectionFactor
  ring

theorem einastoSuperGaussianCorrection_integral (d l k σ r : ℝ) :
    einastoSuperGaussianCorrection d l k σ r = (∫ s in 0..r, 8 * Real.pi * s ^ 2 * einastoSuperGaussianSource d l k σ s) / r := by
  by_cases hr : r = 0
  · subst r
    simp only [einastoSuperGaussianCorrection_center, intervalIntegral.integral_same, zero_div]
  · apply (eq_div_iff hr).mpr
    simpa only [mul_comm] using einastoSuperGaussianCorrection_primitive d l k σ r

/-- The constructed correction is equation (15) with the actual curvature source. -/
theorem einastoSuperGaussianCorrection_actual_integral (d l k σ t : ℝ) :
    einastoSuperGaussianCorrection d l k σ (exp t) =
      (∫ s in 0..exp t, 8 * Real.pi * s ^ 2 * quadraticRadialSource σ (einastoMetric d l (einastoSuperGaussianShape k)) s) / exp t := by
  rw [einastoSuperGaussianCorrection_integral]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (exp_pos t).le
  intro s hs
  have h := einastoSuperGaussianSource_actual d l k σ (log s)
  rw [exp_log hs.1] at h
  dsimp only
  rw [h]

/-- The literal printed appendix also gives this regular inverse near zero. -/
theorem einastoSuperGaussianCorrection_appendix_integral (d l k : ℝ) :
    (fun t => einastoSuperGaussianCorrection d l k (-1) (exp t)) =ᶠ[atBot]
      (fun t => (∫ s in 0..exp t, 8 * Real.pi * s ^ 2 * quadraticAppendixSource (einastoMetric d l (einastoSuperGaussianShape k)) s) / exp t) := by
  obtain ⟨T, hT⟩ := eventually_atBot.mp (einastoSuperGaussianSource_appendix_eventually d l k)
  filter_upwards [eventually_le_atBot T] with t ht
  rw [einastoSuperGaussianCorrection_integral]
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

theorem einastoSuperGaussianCorrection_primitive_hasDerivAt (d l k σ r : ℝ) :
    HasDerivAt (fun s => s * einastoSuperGaussianCorrection d l k σ s)
      (8 * Real.pi * r ^ 2 * einastoSuperGaussianSource d l k σ r) r := by
  have hc : Continuous (fun s : ℝ => 8 * Real.pi * s ^ 2 * einastoSuperGaussianSource d l k σ s) :=
    (continuous_const.mul (continuous_id.pow 2)).mul (einastoSuperGaussianSource_continuous d l k σ)
  have he : (fun s => s * einastoSuperGaussianCorrection d l k σ s) =
      (fun s => ∫ u in 0..s, 8 * Real.pi * u ^ 2 * einastoSuperGaussianSource d l k σ u) := by
    funext s
    exact einastoSuperGaussianCorrection_primitive d l k σ s
  rw [he]
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem einastoSuperGaussianCorrection_source_ode (d l k σ t : ℝ) :
    HasDerivAt (fun r => r * einastoSuperGaussianCorrection d l k σ r)
      (8 * Real.pi * exp t ^ 2 * quadraticRadialSource σ (einastoMetric d l (einastoSuperGaussianShape k)) (exp t)) (exp t) := by
  rw [einastoSuperGaussianSource_actual]
  exact einastoSuperGaussianCorrection_primitive_hasDerivAt d l k σ (exp t)

theorem einastoSuperGaussianCorrection_hasDerivAt (d l k σ t : ℝ) :
    HasDerivAt (einastoSuperGaussianCorrection d l k σ)
      (exp t * (8 * Real.pi * einastoSuperGaussianSource d l k σ (exp t) - einastoSuperGaussianCorrectionFactor d l k σ (exp t))) (exp t) := by
  have h := (einastoSuperGaussianCorrection_primitive_hasDerivAt d l k σ (exp t)).div
    (hasDerivAt_id (exp t)) (exp_ne_zero t)
  have he : (fun r => r * einastoSuperGaussianCorrection d l k σ r / r) = einastoSuperGaussianCorrection d l k σ := by
    funext r
    by_cases hr : r = 0
    · simp [hr, einastoSuperGaussianCorrection_center]
    · field_simp
  simp only [Pi.div_def, id_eq] at h
  rw [he] at h
  apply h.congr_deriv
  unfold einastoSuperGaussianCorrection
  field_simp

/-- Differentiating the exact quotient gives the correction factor's derivative. -/
theorem einastoSuperGaussianCorrectionFactor_hasDerivAt (d l k σ t : ℝ) :
    HasDerivAt (einastoSuperGaussianCorrectionFactor d l k σ)
      ((8 * Real.pi * einastoSuperGaussianSource d l k σ (exp t) - 3 * einastoSuperGaussianCorrectionFactor d l k σ (exp t)) / exp t) (exp t) := by
  have h := (einastoSuperGaussianCorrection_hasDerivAt d l k σ t).div
    ((hasDerivAt_id (exp t)).pow 2) (pow_ne_zero 2 (exp_ne_zero t))
  simp only [Pi.div_def, Pi.pow_apply, id_eq] at h
  have hd : HasDerivAt (fun r => einastoSuperGaussianCorrection d l k σ r / r ^ 2)
      ((8 * Real.pi * einastoSuperGaussianSource d l k σ (exp t) - 3 * einastoSuperGaussianCorrectionFactor d l k σ (exp t)) / exp t) (exp t) := by
    apply h.congr_deriv
    unfold einastoSuperGaussianCorrection
    norm_num only [Nat.cast_ofNat, pow_one]
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  unfold einastoSuperGaussianCorrection
  field_simp [hr.ne']

/-- The actual second derivative is controlled by the proved source derivative. -/
theorem einastoSuperGaussianCorrection_second_hasDerivAt (d l k σ t : ℝ) :
    HasDerivAt (deriv (einastoSuperGaussianCorrection d l k σ))
      (2 * einastoSuperGaussianCorrectionFactor d l k σ (exp t) +
        8 * Real.pi * einastoSuperGaussianSourceEuler d l k σ (exp t)) (exp t) := by
  have h := (hasDerivAt_id (exp t)).mul
    (((einastoSuperGaussianSource_hasDerivAt d l k σ t).const_mul (8 * Real.pi)).sub
      (einastoSuperGaussianCorrectionFactor_hasDerivAt d l k σ t))
  simp only [Pi.mul_def, Pi.sub_def, id_eq] at h
  have hd : HasDerivAt (fun r => r * (8 * Real.pi * einastoSuperGaussianSource d l k σ r - einastoSuperGaussianCorrectionFactor d l k σ r))
      (2 * einastoSuperGaussianCorrectionFactor d l k σ (exp t) + 8 * Real.pi * einastoSuperGaussianSourceEuler d l k σ (exp t)) (exp t) := by
    apply h.congr_deriv
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoSuperGaussianCorrection_hasDerivAt d l k σ (log r)).deriv
  simpa only [exp_log hr] using he

/-- The actual correction has a finite quadratic coefficient for every exponent above two. -/
theorem einastoSuperGaussianCorrection_quadratic_limit (d l k σ : ℝ) :
    Tendsto (fun t => einastoSuperGaussianCorrection d l k σ (exp t) / exp t ^ 2) atBot
      (𝓝 (einastoSuperGaussianCorrectionCoefficient d l k σ)) := by
  have he : (fun t => einastoSuperGaussianCorrection d l k σ (exp t) / exp t ^ 2) =
      (fun t => einastoSuperGaussianCorrectionFactor d l k σ (exp t)) := by
    funext t
    unfold einastoSuperGaussianCorrection
    field_simp
  rw [he, ← einastoSuperGaussianCorrectionFactor_core d l k σ]
  exact (einastoSuperGaussianCorrectionFactor_continuous d l k σ).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoSuperGaussianCorrection_scaled_derivative_limit (d l k σ : ℝ) :
    Tendsto (fun t => deriv (einastoSuperGaussianCorrection d l k σ) (exp t) / exp t) atBot
      (𝓝 (2 * einastoSuperGaussianCorrectionCoefficient d l k σ)) := by
  have he : (fun t => deriv (einastoSuperGaussianCorrection d l k σ) (exp t) / exp t) =
      (fun t => 8 * Real.pi * einastoSuperGaussianSource d l k σ (exp t) - einastoSuperGaussianCorrectionFactor d l k σ (exp t)) := by
    funext t
    rw [(einastoSuperGaussianCorrection_hasDerivAt d l k σ t).deriv]
    field_simp
  rw [he]
  have hS := ((einastoSuperGaussianSource_continuous d l k σ).continuousAt.tendsto.comp tendsto_exp_atBot).const_mul (8 * Real.pi)
  have hG := (einastoSuperGaussianCorrectionFactor_continuous d l k σ).continuousAt.tendsto.comp tendsto_exp_atBot
  rw [einastoSuperGaussianCorrectionFactor_core] at hG
  have h := hS.sub hG
  simp only [Function.comp_apply] at h
  have hc : 8 * Real.pi * einastoSuperGaussianSource d l k σ 0 - einastoSuperGaussianCorrectionCoefficient d l k σ =
      2 * einastoSuperGaussianCorrectionCoefficient d l k σ := by
    unfold einastoSuperGaussianCorrectionCoefficient
    ring
  rw [hc] at h
  exact h

theorem einastoSuperGaussianCorrection_second_derivative_limit (d l k σ : ℝ) :
    Tendsto (fun t => deriv (deriv (einastoSuperGaussianCorrection d l k σ)) (exp t)) atBot
      (𝓝 (2 * einastoSuperGaussianCorrectionCoefficient d l k σ)) := by
  have he : (fun t => deriv (deriv (einastoSuperGaussianCorrection d l k σ)) (exp t)) =
      (fun t => 2 * einastoSuperGaussianCorrectionFactor d l k σ (exp t) + 8 * Real.pi * einastoSuperGaussianSourceEuler d l k σ (exp t)) := by
    funext t
    exact (einastoSuperGaussianCorrection_second_hasDerivAt d l k σ t).deriv
  rw [he]
  have hG := einastoSuperGaussianCorrectionFactor_continuous d l k σ
  have hS := einastoSuperGaussianSourceEuler_continuous d l k σ
  have hc : Continuous (fun r : ℝ => 2 * einastoSuperGaussianCorrectionFactor d l k σ r + 8 * Real.pi * einastoSuperGaussianSourceEuler d l k σ r) := by
    fun_prop
  simpa [Function.comp_def, einastoSuperGaussianCorrectionFactor_core, einastoSuperGaussianSourceEuler_core] using hc.continuousAt.tendsto.comp tendsto_exp_atBot

end GaloisForLFunctions.HTGeometry
