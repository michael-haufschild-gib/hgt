import GaloisForLFunctions.HTGeometry.EinastoExponentialCurvature

/-!
# The actual exponential Einasto source has a first-order radial pole

Track both signs of the algebraic R² term in arXiv:2608.23600, equations (6)
and (26), using unrestricted real sign data σ. The unfactored radial source
contains the actual metric curvature and its first two derivatives. Its pole
coefficient is independent of σ. For the printed appendix, equality with the
unfactored source is established near the center, where the actual lapse is
strictly positive; no division across a horizon is silently cancelled.
-/
noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Radial source with the algebraic curvature sign exposed and derivative terms unfactored. -/
def quadraticRadialSource (σ : ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (2 * radialRicciScalar f r * (8 * Real.pi * radialEinsteinDensity f r) +
      σ * radialRicciScalar f r ^ (2 : ℕ) / 2 -
      2 * f r * deriv (deriv (radialRicciScalar f)) r -
      (4 * f r / r + deriv f r) * deriv (radialRicciScalar f) r) / (8 * Real.pi)

/-- The regular extension of r times the curvature source. -/
def einastoQuadraticPoleWeight (d l σ r : ℝ) : ℝ :=
  (r * (2 * einastoExponentialRicci d l r * (8 * Real.pi * einastoDensity d l 0 r) +
      σ * einastoExponentialRicci d l r ^ (2 : ℕ) / 2 -
      2 * einastoMetric d l 0 r * einastoExponentialRicciSecond d l r -
      einastoExponentialMetricSlope d l r * einastoExponentialRicciSlope d l r) -
      4 * einastoMetric d l 0 r * einastoExponentialRicciSlope d l r) / (8 * Real.pi)

theorem einastoQuadraticPoleWeight_continuous (d l σ : ℝ) :
    Continuous (einastoQuadraticPoleWeight d l σ) := by
  have hR := einastoExponentialRicci_continuous d l
  have hD := einastoDensity_continuous d l 0
  have hf := einastoMetric_continuous d l 0
  have hR1 := einastoExponentialRicciSlope_continuous d l
  have hR2 := einastoExponentialRicciSecond_continuous d l
  have hf1 := einastoExponentialMetricSlope_continuous d l
  unfold einastoQuadraticPoleWeight
  fun_prop (disch := exact Real.pi_ne_zero)

theorem einastoQuadraticPoleWeight_core (d l σ : ℝ) :
    einastoQuadraticPoleWeight d l σ 0 = -20 * Real.exp d / Real.exp l := by
  unfold einastoQuadraticPoleWeight
  rw [einastoMetric_zero, einastoExponentialRicciSlope_core]
  simp only [zero_mul, zero_sub, mul_one]
  field_simp
  ring

/-- The pole coefficient is forced by the actual third and fourth metric derivatives. -/
theorem einastoQuadraticPoleWeight_source (d l σ t : ℝ) :
    Real.exp t * quadraticRadialSource σ (einastoMetric d l 0) (Real.exp t) =
      einastoQuadraticPoleWeight d l σ (Real.exp t) := by
  unfold quadraticRadialSource
  rw [einastoExponentialRicci_actual, radialEinsteinDensity_einasto,
    einastoExponentialRicci_actual_derivative, einastoExponentialRicci_actual_second_derivative,
    einastoExponentialMetricSlope_actual]
  unfold einastoQuadraticPoleWeight
  field_simp
  ring

/-- In particular, the pole survives both printed choices of the quadratic algebraic sign. -/
theorem einastoQuadraticSource_pole_limit (d l σ : ℝ) :
    Tendsto (fun t => Real.exp t * quadraticRadialSource σ (einastoMetric d l 0) (Real.exp t)) atBot
      (𝓝 (-20 * Real.exp d / Real.exp l)) := by
  have he : (fun t => Real.exp t * quadraticRadialSource σ (einastoMetric d l 0) (Real.exp t)) =
      (fun t => einastoQuadraticPoleWeight d l σ (Real.exp t)) := by
    funext t
    exact einastoQuadraticPoleWeight_source d l σ t
  rw [he, ← einastoQuadraticPoleWeight_core d l σ]
  exact (einastoQuadraticPoleWeight_continuous d l σ).continuousAt.tendsto.comp Real.tendsto_exp_atBot

/-- Extract the literal first-order density source from equation (26). -/
def quadraticAppendixSource (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (fun β => quadraticAppendixTT f β r / (8 * Real.pi)) 0

theorem quadraticAppendixSource_eq (f : ℝ → ℝ) (r : ℝ) :
    quadraticAppendixSource f r =
      (deriv (fun s => s * (1 - f s)) r / r ^ (2 : ℕ) * (2 * radialRicciScalar f r) -
        2 * f r * ((2 / r + deriv f r / (2 * f r)) * deriv (radialRicciScalar f) r +
          deriv (deriv (radialRicciScalar f)) r) - radialRicciScalar f r ^ (2 : ℕ) / 2) / (8 * Real.pi) := by
  unfold quadraticAppendixSource quadraticAppendixTT
  have h := (((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (radialRicciScalar f r)).const_add 1).const_mul
    (deriv (fun s => s * (1 - f s)) r / r ^ (2 : ℕ))).sub
    ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (f r)).mul_const
      ((2 / r + deriv f r / (2 * f r)) * deriv (radialRicciScalar f) r +
        deriv (deriv (radialRicciScalar f)) r))
  have h' := (h.sub (((hasDerivAt_id (0 : ℝ)).mul_const (radialRicciScalar f r ^ (2 : ℕ))).div_const 2)).div_const (8 * Real.pi)
  simp only [Pi.sub_def, id_eq] at h'
  rw [h'.deriv]
  ring

/-- The actual lapse is nonzero on a whole positive neighborhood of its regular center. -/
theorem einastoExponentialMetric_eventually_pos (d l : ℝ) :
    ∀ᶠ t in atBot, 0 < einastoMetric d l 0 (Real.exp t) := by
  have h := (einastoMetric_flat_core_limit d l 0).comp Real.tendsto_exp_atBot
  exact h.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))

/-- Near the center, the printed appendix source equals the minus-sign unfactored source. -/
theorem quadraticAppendixSource_einasto_eventually (d l : ℝ) :
    (fun t => quadraticAppendixSource (einastoMetric d l 0) (Real.exp t)) =ᶠ[atBot]
      (fun t => quadraticRadialSource (-1) (einastoMetric d l 0) (Real.exp t)) := by
  filter_upwards [einastoExponentialMetric_eventually_pos d l] with t ht
  have hd := (hasDerivAt_id (Real.exp t)).mul ((einastoMetric_derivative d l 0 t).const_sub 1)
  simp only [Pi.mul_def, id_eq] at hd
  rw [quadraticAppendixSource_eq, hd.deriv]
  unfold quadraticRadialSource radialEinsteinDensity
  rw [(einastoMetric_derivative d l 0 t).deriv]
  field_simp [ht.ne']
  ring

/-- The pole is present in the paper's literal appendix, independently of the algebraic sign audit. -/
theorem quadraticAppendixSource_einasto_pole_limit (d l : ℝ) :
    Tendsto (fun t => Real.exp t * quadraticAppendixSource (einastoMetric d l 0) (Real.exp t)) atBot
      (𝓝 (-20 * Real.exp d / Real.exp l)) := by
  apply (einastoQuadraticSource_pole_limit d l (-1)).congr'
  filter_upwards [quadraticAppendixSource_einasto_eventually d l] with t ht
  rw [ht]

/-- The existing integral core is differentiable at every positive radius. -/
theorem einastoCore_differentiableAt (d l a t : ℝ) :
    DifferentiableAt ℝ (einastoCore d l a) (Real.exp t) := by
  have h := (einastoMass_derivative d l a (Real.exp t)).differentiableAt.div
    (differentiableAt_id.pow 3) (by positivity : Real.exp t ^ (3 : ℕ) ≠ 0)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (Real.exp_pos t)] with r hr
  change einastoCore d l a r = einastoMass d l a r / r ^ (3 : ℕ)
  rw [einastoMass_core]
  field_simp [hr.ne']

/-- The pole weight is differentiable away from the center, so its radial inverse is twice differentiable. -/
theorem einastoQuadraticPoleWeight_differentiableAt (d l σ t : ℝ) :
    DifferentiableAt ℝ (einastoQuadraticPoleWeight d l σ) (Real.exp t) := by
  have hD := (einastoDensity_exponential_hasDerivAt d l (Real.exp t)).differentiableAt
  have hF := (einastoMetric_derivative d l 0 t).differentiableAt
  have hC := einastoCore_differentiableAt d l 0 t
  unfold einastoQuadraticPoleWeight einastoExponentialRicci einastoExponentialRicciSlope
    einastoExponentialRicciSecond einastoExponentialMetricSlope
  fun_prop

end GaloisForLFunctions.HTGeometry
