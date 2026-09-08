import GaloisForLFunctions.HTGeometry.EinastoQuadraticPoleSource

/-!
# Continuous metric derivative extensions for all Einasto shapes

The actual first and second radial derivatives from arXiv:2608.23600 have
continuous extensions through the center, for every positive density, length
scale and shape parameter. These extensions let curvature-source derivatives
be analyzed without introducing independent, assumed metric jets.
The literal appendix-to-unfactored-source identity is generalized from the
exponential profile to every Einasto shape near its regular center.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoMetricFirstJet (d l a r : ℝ) : ℝ :=
  r * (2 * einastoCore d l a r - 8 * Real.pi * einastoDensity d l a r)

def einastoMetricSecondJet (d l a r : ℝ) : ℝ :=
  -4 * einastoCore d l a r + 8 * Real.pi * einastoSlope d l a r

theorem einastoMetricFirstJet_actual (d l a t : ℝ) :
    deriv (einastoMetric d l a) (exp t) = einastoMetricFirstJet d l a (exp t) := by
  rw [(einastoMetric_derivative d l a t).deriv, einastoMass_core]
  unfold einastoMetricFirstJet
  field_simp

theorem einastoMetricSecondJet_actual (d l a t : ℝ) :
    deriv (deriv (einastoMetric d l a)) (exp t) = einastoMetricSecondJet d l a (exp t) :=
  (einastoMetric_second_derivative d l a t).deriv

theorem einastoMetricFirstJet_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (einastoMetric d l a) (einastoMetricFirstJet d l a (exp t)) (exp t) := by
  have h := einastoMetric_derivative d l a t
  apply h.congr_deriv
  rw [← h.deriv]
  exact einastoMetricFirstJet_actual d l a t

theorem einastoMetricSecondJet_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (einastoMetricFirstJet d l a) (einastoMetricSecondJet d l a (exp t)) (exp t) := by
  apply (einastoMetric_second_derivative d l a t).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have h := einastoMetricFirstJet_actual d l a (log r)
  simpa only [exp_log hr] using h.symm

theorem einastoMetricFirstJet_continuous (d l a : ℝ) : Continuous (einastoMetricFirstJet d l a) :=
  continuous_id.mul ((continuous_const.mul (einastoCore_continuous d l a)).sub
    (continuous_const.mul (einastoDensity_continuous d l a)))

theorem einastoMetricSecondJet_continuous (d l a : ℝ) : Continuous (einastoMetricSecondJet d l a) :=
  (continuous_const.mul (einastoCore_continuous d l a)).add
    (continuous_const.mul (einastoSlope_continuous d l a))

theorem einastoMetricFirstJet_core (d l a : ℝ) : einastoMetricFirstJet d l a 0 = 0 := by
  unfold einastoMetricFirstJet
  ring

theorem einastoMetricSecondJet_core (d l a : ℝ) :
    einastoMetricSecondJet d l a 0 = -16 * Real.pi * exp d / 3 := by
  unfold einastoMetricSecondJet
  rw [einastoCore_zero, einastoSlope_zero]
  ring

theorem einastoMetricFirstJet_core_limit (d l a : ℝ) :
    Tendsto (fun t => deriv (einastoMetric d l a) (exp t)) atBot (𝓝 0) := by
  have he : (fun t => deriv (einastoMetric d l a) (exp t)) =
      (fun t => einastoMetricFirstJet d l a (exp t)) := by
    funext t
    exact einastoMetricFirstJet_actual d l a t
  rw [he, ← einastoMetricFirstJet_core d l a]
  exact (einastoMetricFirstJet_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoMetricSecondJet_core_limit (d l a : ℝ) :
    Tendsto (fun t => deriv (deriv (einastoMetric d l a)) (exp t)) atBot
      (𝓝 (-16 * Real.pi * exp d / 3)) := by
  have he : (fun t => deriv (deriv (einastoMetric d l a)) (exp t)) =
      (fun t => einastoMetricSecondJet d l a (exp t)) := by
    funext t
    exact einastoMetricSecondJet_actual d l a t
  rw [he, ← einastoMetricSecondJet_core d l a]
  exact (einastoMetricSecondJet_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot

/-- The literal appendix identity holds on a whole central neighborhood for every shape. -/
theorem quadraticAppendixSource_einasto_all_shapes_eventually (d l a : ℝ) :
    (fun t => quadraticAppendixSource (einastoMetric d l a) (exp t)) =ᶠ[atBot]
      (fun t => quadraticRadialSource (-1) (einastoMetric d l a) (exp t)) := by
  have hp : ∀ᶠ t in atBot, 0 < einastoMetric d l a (exp t) :=
    ((einastoMetric_flat_core_limit d l a).comp tendsto_exp_atBot).eventually
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hp] with t ht
  have hd := (hasDerivAt_id (exp t)).mul ((einastoMetric_derivative d l a t).const_sub 1)
  simp only [Pi.mul_def, id_eq] at hd
  rw [quadraticAppendixSource_eq, hd.deriv]
  unfold quadraticRadialSource radialEinsteinDensity
  rw [(einastoMetric_derivative d l a t).deriv]
  field_simp [ht.ne']
  ring

end GaloisForLFunctions.HTGeometry
