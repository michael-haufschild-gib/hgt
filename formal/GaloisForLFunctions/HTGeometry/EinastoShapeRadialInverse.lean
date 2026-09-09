import GaloisForLFunctions.HTGeometry.EinastoPowerRadialInverse
import GaloisForLFunctions.HTGeometry.EinastoDefectRadialInverse

/-!
# The actual quadratic radial inverse for every Einasto shape

Combine the power-law inverse and the bounded algebraic defect. The resulting
correction equals equation (15) with the actual radial source, for every
positive shape exponent and either algebraic sign. Its first two derivatives
are actual derivatives of that integral. The same construction matches the
literal appendix near the center, and its metric stays continuous and positive
there even on the side where central curvature may diverge.
-/
noncomputable section
open Filter Real Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoShapeCorrection (d l a σ r : ℝ) : ℝ :=
  einastoPowerCorrection d l a r + einastoDefectCorrection d l a σ r

def einastoShapePerturbedMetric (d l a σ β r : ℝ) : ℝ :=
  einastoMetric d l a r + β * einastoShapeCorrection d l a σ r

theorem einastoShapeCorrection_continuous (d l a σ : ℝ) : Continuous (einastoShapeCorrection d l a σ) :=
  (einastoPowerCorrection_continuous d l a).add (einastoDefectCorrection_continuous d l a σ)

theorem einastoShapeCorrection_center (d l a σ : ℝ) : einastoShapeCorrection d l a σ 0 = 0 := by
  rw [einastoShapeCorrection, einastoPowerCorrection_center, einastoDefectCorrection_center, zero_add]

theorem einastoShapeCorrection_corrected_sign (d l a r : ℝ) :
    einastoShapeCorrection d l a 1 r = einastoPowerCorrection d l a r := by
  rw [einastoShapeCorrection, einastoDefectCorrection_corrected_sign, add_zero]

/-- A continuous weighted source underlies the integral even when the unweighted source diverges. -/
theorem einastoShapeCorrection_integral (d l a σ t : ℝ) :
    einastoShapeCorrection d l a σ (exp t) =
      (∫ v in 0..exp t, 8 * Real.pi * einastoProfilePower l a v * einastoShapeSourceFactor d l a v +
        8 * Real.pi * v ^ 2 * einastoShapeSourceDefect d l a σ v) / exp t := by
  have hP : Continuous (fun v : ℝ => 8 * Real.pi * einastoProfilePower l a v * einastoShapeSourceFactor d l a v) :=
    (continuous_const.mul (einastoProfilePower_continuous l a)).mul (einastoShapeSourceFactor_continuous d l a)
  have hD : Continuous (fun v : ℝ => 8 * Real.pi * v ^ 2 * einastoShapeSourceDefect d l a σ v) :=
    (continuous_const.mul (continuous_id.pow 2)).mul (einastoShapeSourceDefect_continuous d l a σ)
  rw [einastoShapeCorrection, einastoPowerCorrection_integral, einastoDefectCorrection_integral,
    intervalIntegral.integral_add (hP.intervalIntegrable 0 (exp t)) (hD.intervalIntegrable 0 (exp t)), add_div]

/-- Identification with the paper's actual radial source, with neither regularity nor boundedness assumed. -/
theorem einastoShapeCorrection_actual_integral (d l a σ t : ℝ) :
    einastoShapeCorrection d l a σ (exp t) =
      (∫ v in 0..exp t, 8 * Real.pi * v ^ 2 * quadraticRadialSource σ (einastoMetric d l a) v) / exp t := by
  rw [einastoShapeCorrection_integral]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (exp_pos t).le
  intro v hv
  have h := einastoShapeSource_decomposition d l a σ (log v)
  rw [exp_log hv.1] at h
  dsimp only
  rw [h]
  field_simp [hv.1.ne']

/-- The literal appendix integral is included for every shape, on a whole central neighborhood. -/
theorem einastoShapeCorrection_appendix_integral (d l a : ℝ) :
    (fun t => einastoShapeCorrection d l a (-1) (exp t)) =ᶠ[atBot]
      (fun t => (∫ v in 0..exp t, 8 * Real.pi * v ^ 2 * quadraticAppendixSource (einastoMetric d l a) v) / exp t) := by
  obtain ⟨T, hT⟩ := eventually_atBot.mp (quadraticAppendixSource_einasto_all_shapes_eventually d l a)
  filter_upwards [eventually_le_atBot T] with t ht
  rw [einastoShapeCorrection_actual_integral]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (exp_pos t).le
  intro v hv
  have hvt : log v ≤ t := by
    apply exp_le_exp.mp
    rw [exp_log hv.1]
    exact hv.2.le
  have he := hT (log v) (hvt.trans ht)
  dsimp only at he ⊢
  rw [exp_log hv.1] at he
  rw [he]

theorem einastoShapeCorrection_hasDerivAt (d l a σ t : ℝ) :
    HasDerivAt (einastoShapeCorrection d l a σ)
      (deriv (einastoPowerCorrection d l a) (exp t) + deriv (einastoDefectCorrection d l a σ) (exp t)) (exp t) := by
  have hP := einastoPowerCorrection_hasDerivAt d l a t
  have hD := einastoDefectCorrection_hasDerivAt d l a σ t
  unfold einastoShapeCorrection
  rw [hP.deriv, hD.deriv]
  simpa only [Pi.add_def] using hP.add hD

theorem einastoShapeCorrection_second_hasDerivAt (d l a σ t : ℝ) :
    HasDerivAt (deriv (einastoShapeCorrection d l a σ))
      (deriv (deriv (einastoPowerCorrection d l a)) (exp t) + deriv (deriv (einastoDefectCorrection d l a σ)) (exp t)) (exp t) := by
  have hP := einastoPowerCorrection_second_hasDerivAt d l a t
  have hD := einastoDefectCorrection_second_hasDerivAt d l a σ t
  rw [hP.deriv, hD.deriv]
  have h := hP.add hD
  simp only [Pi.add_def] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoShapeCorrection_hasDerivAt d l a σ (log r)).deriv
  simpa only [exp_log hr] using he

/-- The source equation holds for the actually constructed correction on the entire positive ray. -/
theorem einastoShapeCorrection_source_ode (d l a σ t : ℝ) :
    HasDerivAt (fun r => r * einastoShapeCorrection d l a σ r)
      (8 * Real.pi * exp t ^ 2 * quadraticRadialSource σ (einastoMetric d l a) (exp t)) (exp t) := by
  have h := (hasDerivAt_id (exp t)).mul (einastoShapeCorrection_hasDerivAt d l a σ t)
  simp only [Pi.mul_def, id_eq] at h
  apply h.congr_deriv
  rw [einastoShapeSource_decomposition, (einastoPowerCorrection_hasDerivAt d l a t).deriv,
    (einastoDefectCorrection_hasDerivAt d l a σ t).deriv]
  unfold einastoShapeCorrection einastoPowerCorrection einastoDefectCorrection
  field_simp
  ring

theorem einastoShapePerturbedMetric_continuous (d l a σ β : ℝ) : Continuous (einastoShapePerturbedMetric d l a σ β) :=
  (einastoMetric_continuous d l a).add (continuous_const.mul (einastoShapeCorrection_continuous d l a σ))

theorem einastoShapePerturbedMetric_center (d l a σ β : ℝ) : einastoShapePerturbedMetric d l a σ β 0 = 1 := by
  simp only [einastoShapePerturbedMetric, einastoMetric_zero, einastoShapeCorrection_center, mul_zero, add_zero]

theorem einastoShapePerturbedMetric_eventually_pos (d l a σ β : ℝ) :
    ∀ᶠ t in atBot, 0 < einastoShapePerturbedMetric d l a σ β (exp t) := by
  have h := (einastoShapePerturbedMetric_continuous d l a σ β).continuousAt.tendsto.comp tendsto_exp_atBot
  rw [einastoShapePerturbedMetric_center] at h
  exact h.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))

theorem einastoShapePerturbedMetric_hasDerivAt (d l a σ β t : ℝ) :
    HasDerivAt (einastoShapePerturbedMetric d l a σ β)
      (deriv (einastoMetric d l a) (exp t) + β * deriv (einastoShapeCorrection d l a σ) (exp t)) (exp t) := by
  have hf := einastoMetric_derivative d l a t
  have hh := einastoShapeCorrection_hasDerivAt d l a σ t
  unfold einastoShapePerturbedMetric
  rw [hf.deriv, hh.deriv]
  simpa only [Pi.add_def] using hf.add (hh.const_mul β)

theorem einastoShapePerturbedMetric_second_hasDerivAt (d l a σ β t : ℝ) :
    HasDerivAt (deriv (einastoShapePerturbedMetric d l a σ β))
      (deriv (deriv (einastoMetric d l a)) (exp t) + β * deriv (deriv (einastoShapeCorrection d l a σ)) (exp t)) (exp t) := by
  have hf := einastoMetric_second_derivative d l a t
  have hh := einastoShapeCorrection_second_hasDerivAt d l a σ t
  rw [hf.deriv, hh.deriv]
  have h := hf.add (hh.const_mul β)
  simp only [Pi.add_def] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoShapePerturbedMetric_hasDerivAt d l a σ β (log r)).deriv
  simpa only [exp_log hr] using he

theorem einastoShapePerturbedMetric_zero_coupling (d l a σ r : ℝ) :
    einastoShapePerturbedMetric d l a σ 0 r = einastoMetric d l a r := by
  simp only [einastoShapePerturbedMetric, zero_mul, add_zero]

end GaloisForLFunctions.HTGeometry
