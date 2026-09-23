import GaloisForLFunctions.HTGeometry.EinastoQuadraticPoleSource

/-!
# The regular radial integral of the actual exponential Einasto curvature source

Construct equation (15) of arXiv:2608.23600 by a fixed-interval integral. The
source's 1/r pole is integrable after the r² weight: the metric correction is
continuous and vanishes at the center, but starts at linear rather than quadratic
order. Its exact leading coefficient is nonzero for every positive density and
length scale. The literal appendix source gives the same integral near zero.
-/
noncomputable section
open Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Continuous factor obtained by rescaling the radial source integral to [0,1]. -/
def einastoQuadraticCorrectionFactor (d l σ r : ℝ) : ℝ :=
  8 * Real.pi * ∫ u in (0 : ℝ)..1, u * einastoQuadraticPoleWeight d l σ (r * u)

/-- The regular curvature correction selected by the actual radial integral. -/
def einastoQuadraticCorrection (d l σ r : ℝ) : ℝ := r * einastoQuadraticCorrectionFactor d l σ r

theorem einastoQuadraticCorrectionFactor_continuous (d l σ : ℝ) :
    Continuous (einastoQuadraticCorrectionFactor d l σ) := by
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact continuous_snd.mul ((einastoQuadraticPoleWeight_continuous d l σ).comp
    (continuous_fst.mul continuous_snd))

/-- The source pole produces a nonzero linear metric coefficient. -/
theorem einastoQuadraticCorrectionFactor_core (d l σ : ℝ) :
    einastoQuadraticCorrectionFactor d l σ 0 = -80 * Real.pi * exp d / exp l := by
  simp only [einastoQuadraticCorrectionFactor, zero_mul, einastoQuadraticPoleWeight_core]
  rw [intervalIntegral.integral_mul_const]
  have h : (∫ u in (0 : ℝ)..1, u) = (1 : ℝ) / 2 := by
    simp
  rw [h]
  ring

theorem einastoQuadraticCorrection_continuous (d l σ : ℝ) : Continuous (einastoQuadraticCorrection d l σ) :=
  continuous_id.mul (einastoQuadraticCorrectionFactor_continuous d l σ)

theorem einastoQuadraticCorrection_center (d l σ : ℝ) : einastoQuadraticCorrection d l σ 0 = 0 := by
  unfold einastoQuadraticCorrection
  ring

/-- The rescaled construction is the exact radial primitive for every real endpoint. -/
theorem einastoQuadraticCorrection_primitive (d l σ r : ℝ) :
    r * einastoQuadraticCorrection d l σ r =
      ∫ s in 0..r, 8 * Real.pi * s * einastoQuadraticPoleWeight d l σ s := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun s : ℝ => s * einastoQuadraticPoleWeight d l σ s) r (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, mul_one] at h
  rw [show (fun u : ℝ => r * u * einastoQuadraticPoleWeight d l σ (r * u)) =
    (fun u : ℝ => r * (u * einastoQuadraticPoleWeight d l σ (r * u))) by funext u; ring,
    intervalIntegral.integral_const_mul] at h
  rw [show (fun s : ℝ => 8 * Real.pi * s * einastoQuadraticPoleWeight d l σ s) =
    (fun s : ℝ => (8 * Real.pi) * (s * einastoQuadraticPoleWeight d l σ s)) by funext s; ring,
    intervalIntegral.integral_const_mul, ← h]
  unfold einastoQuadraticCorrection einastoQuadraticCorrectionFactor
  ring

theorem einastoQuadraticCorrection_integral (d l σ r : ℝ) :
    einastoQuadraticCorrection d l σ r =
      (∫ s in 0..r, 8 * Real.pi * s * einastoQuadraticPoleWeight d l σ s) / r := by
  by_cases hr : r = 0
  · subst r
    simp only [einastoQuadraticCorrection_center, intervalIntegral.integral_same, zero_div]
  · apply (eq_div_iff hr).mpr
    simpa only [mul_comm] using einastoQuadraticCorrection_primitive d l σ r

/-- Identification with equation (15), using the actual curvature source. -/
theorem einastoQuadraticCorrection_actual_integral (d l σ t : ℝ) :
    einastoQuadraticCorrection d l σ (exp t) =
      (∫ s in 0..exp t, 8 * Real.pi * s ^ (2 : ℕ) * quadraticRadialSource σ (einastoMetric d l 0) s) / exp t := by
  rw [einastoQuadraticCorrection_integral]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (exp_pos t).le
  intro s hs
  have h := einastoQuadraticPoleWeight_source d l σ (log s)
  rw [exp_log hs.1] at h
  dsimp only
  rw [← h]
  ring

/-- The printed appendix yields the very same regular integral in a whole central neighborhood. -/
theorem einastoQuadraticCorrection_appendix_integral (d l : ℝ) :
    (fun t => einastoQuadraticCorrection d l (-1) (exp t)) =ᶠ[atBot]
      (fun t => (∫ s in 0..exp t, 8 * Real.pi * s ^ (2 : ℕ) * quadraticAppendixSource (einastoMetric d l 0) s) / exp t) := by
  obtain ⟨T, hT⟩ := eventually_atBot.mp (quadraticAppendixSource_einasto_eventually d l)
  filter_upwards [eventually_le_atBot T] with t ht
  rw [einastoQuadraticCorrection_actual_integral]
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

/-- The actual radial primitive satisfies the source ODE. -/
theorem einastoQuadraticCorrection_primitive_hasDerivAt (d l σ r : ℝ) :
    HasDerivAt (fun s => s * einastoQuadraticCorrection d l σ s)
      (8 * Real.pi * r * einastoQuadraticPoleWeight d l σ r) r := by
  have hc : Continuous (fun s : ℝ => 8 * Real.pi * s * einastoQuadraticPoleWeight d l σ s) :=
    (continuous_const.mul continuous_id).mul (einastoQuadraticPoleWeight_continuous d l σ)
  have he : (fun s => s * einastoQuadraticCorrection d l σ s) =
      (fun s => ∫ u in 0..s, 8 * Real.pi * u * einastoQuadraticPoleWeight d l σ u) := by
    funext s
    exact einastoQuadraticCorrection_primitive d l σ s
  rw [he]
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem einastoQuadraticCorrection_source_ode (d l σ t : ℝ) :
    HasDerivAt (fun r => r * einastoQuadraticCorrection d l σ r)
      (8 * Real.pi * exp t ^ (2 : ℕ) * quadraticRadialSource σ (einastoMetric d l 0) (exp t)) (exp t) := by
  apply (einastoQuadraticCorrection_primitive_hasDerivAt d l σ (exp t)).congr_deriv
  rw [← einastoQuadraticPoleWeight_source]
  ring

/-- Actual first derivative of the metric correction, obtained from the integral quotient. -/
theorem einastoQuadraticCorrection_hasDerivAt (d l σ t : ℝ) :
    HasDerivAt (einastoQuadraticCorrection d l σ)
      (8 * Real.pi * einastoQuadraticPoleWeight d l σ (exp t) -
        einastoQuadraticCorrectionFactor d l σ (exp t)) (exp t) := by
  have h := (einastoQuadraticCorrection_primitive_hasDerivAt d l σ (exp t)).div
    (hasDerivAt_id (exp t)) (exp_ne_zero t)
  have he : (fun r => r * einastoQuadraticCorrection d l σ r / r) = einastoQuadraticCorrection d l σ := by
    funext r
    by_cases hr : r = 0
    · simp [hr, einastoQuadraticCorrection_center]
    · field_simp
  simp only [Pi.div_def, id_eq] at h
  rw [he] at h
  apply h.congr_deriv
  unfold einastoQuadraticCorrection
  field_simp

/-- The normalized correction converges to a strictly negative coefficient. -/
theorem einastoQuadraticCorrection_linear_limit (d l σ : ℝ) :
    Tendsto (fun t => einastoQuadraticCorrection d l σ (exp t) / exp t) atBot
      (𝓝 (-80 * Real.pi * exp d / exp l)) := by
  have he : (fun t => einastoQuadraticCorrection d l σ (exp t) / exp t) =
      (fun t => einastoQuadraticCorrectionFactor d l σ (exp t)) := by
    funext t
    unfold einastoQuadraticCorrection
    field_simp
  rw [he, ← einastoQuadraticCorrectionFactor_core d l σ]
  exact (einastoQuadraticCorrectionFactor_continuous d l σ).continuousAt.tendsto.comp tendsto_exp_atBot

/-- Finiteness at zero follows despite the nonzero first-order metric term. -/
theorem einastoQuadraticCorrection_limit (d l σ : ℝ) :
    Tendsto (einastoQuadraticCorrection d l σ) (𝓝 0) (𝓝 0) := by
  simpa only [einastoQuadraticCorrection_center] using
    (einastoQuadraticCorrection_continuous d l σ).continuousAt.tendsto (x := 0)

/-- The divided correction factor is differentiable at every positive radius. -/
theorem einastoQuadraticCorrectionFactor_differentiableAt (d l σ t : ℝ) :
    DifferentiableAt ℝ (einastoQuadraticCorrectionFactor d l σ) (exp t) := by
  have h := (einastoQuadraticCorrection_hasDerivAt d l σ t).differentiableAt.div
    differentiableAt_id (exp_ne_zero t)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  change einastoQuadraticCorrectionFactor d l σ r = einastoQuadraticCorrection d l σ r / r
  unfold einastoQuadraticCorrection
  field_simp [hr.ne']

/-- The constructed correction is twice differentiable on the entire positive ray. -/
theorem einastoQuadraticCorrection_twice_differentiable (d l σ t : ℝ) :
    DifferentiableAt ℝ (deriv (einastoQuadraticCorrection d l σ)) (exp t) := by
  have h := ((einastoQuadraticPoleWeight_differentiableAt d l σ t).const_mul (8 * Real.pi)).sub
    (einastoQuadraticCorrectionFactor_differentiableAt d l σ t)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoQuadraticCorrection_hasDerivAt d l σ (log r)).deriv
  simpa only [exp_log hr, Pi.sub_apply] using he

end GaloisForLFunctions.HTGeometry
