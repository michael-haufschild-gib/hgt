import GaloisForLFunctions.HTGeometry.EinastoGaussianCurvature

/-!
# The Gaussian Einasto quadratic source has a regular central extension

In the shape-one profile, R'/r generated a pole. For the Gaussian profile,
R'/r is an explicit smooth function. Substitute the actual curvature derivatives
into arXiv:2608.23600's radial source, track either algebraic R² sign, and prove
both the source and its positive-ray derivative have continuous extensions.
The source's central value is determined exactly; it is not supplied as an
assumption to the radial correction theorem.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Regular extension of the actual Gaussian curvature source through the center. -/
def einastoGaussianSource (d l σ r : ℝ) : ℝ :=
  2 * einastoGaussianRicci d l r * einastoDensity d l einastoGaussianShape r +
    σ * einastoGaussianRicci d l r ^ (2 : ℕ) / (16 * Real.pi) -
    einastoMetric d l einastoGaussianShape r * einastoGaussianRicciSecond d l r / (4 * Real.pi) -
    einastoMetric d l einastoGaussianShape r * einastoGaussianRicciSlopeQuotient d l r / (2 * Real.pi) -
    einastoMetricFirstJet d l einastoGaussianShape r * einastoGaussianRicciSlope d l r / (8 * Real.pi)

/-- Continuous extension of the source's actual positive-radius derivative. -/
def einastoGaussianSourceSlope (d l σ r : ℝ) : ℝ :=
  2 * (einastoGaussianRicciSlope d l r * einastoDensity d l einastoGaussianShape r +
      einastoGaussianRicci d l r * einastoGaussianDensitySlope d l r) +
    σ * (2 * einastoGaussianRicci d l r * einastoGaussianRicciSlope d l r) / (16 * Real.pi) -
    (einastoMetricFirstJet d l einastoGaussianShape r * einastoGaussianRicciSecond d l r +
      einastoMetric d l einastoGaussianShape r * einastoGaussianRicciThird d l r) / (4 * Real.pi) -
    (einastoMetricFirstJet d l einastoGaussianShape r * einastoGaussianRicciSlopeQuotient d l r +
      einastoMetric d l einastoGaussianShape r * einastoGaussianRicciQuotientSlope d l r) / (2 * Real.pi) -
    (einastoMetricSecondJet d l einastoGaussianShape r * einastoGaussianRicciSlope d l r +
      einastoMetricFirstJet d l einastoGaussianShape r * einastoGaussianRicciSecond d l r) / (8 * Real.pi)

/-- The apparent radial pole cancels using the actual R' factor, not an imposed boundary condition. -/
theorem einastoGaussianSource_actual (d l σ t : ℝ) :
    quadraticRadialSource σ (einastoMetric d l einastoGaussianShape) (exp t) =
      einastoGaussianSource d l σ (exp t) := by
  unfold quadraticRadialSource
  rw [einastoGaussianRicci_actual, radialEinsteinDensity_einasto,
    einastoGaussianRicci_actual_derivative, einastoGaussianRicci_actual_second_derivative,
    einastoMetricFirstJet_actual]
  unfold einastoGaussianSource einastoGaussianRicciSlope
  field_simp
  ring

theorem einastoGaussianSource_continuous (d l σ : ℝ) : Continuous (einastoGaussianSource d l σ) := by
  have hR := einastoGaussianRicci_continuous d l
  have hD := einastoDensity_continuous d l einastoGaussianShape
  have hf := einastoMetric_continuous d l einastoGaussianShape
  have hR2 := einastoGaussianRicciSecond_continuous d l
  have hS := einastoGaussianRicciQuotient_continuous d l
  have hf1 := einastoMetricFirstJet_continuous d l einastoGaussianShape
  have hR1 := einastoGaussianRicciSlope_continuous d l
  unfold einastoGaussianSource
  fun_prop

/-- All derivative terms in the source are differentiated from proved actual metric data. -/
theorem einastoGaussianSource_hasDerivAt (d l σ t : ℝ) :
    HasDerivAt (einastoGaussianSource d l σ) (einastoGaussianSourceSlope d l σ (exp t)) (exp t) := by
  have hR := einastoGaussianRicci_hasDerivAt d l (exp t)
  have hD := einastoDensity_gaussian_hasDerivAt d l (exp t)
  have hf := einastoMetricFirstJet_hasDerivAt d l einastoGaussianShape t
  have hR2 := einastoGaussianRicciSecond_hasDerivAt d l (exp t)
  have hS := einastoGaussianRicciQuotient_hasDerivAt d l (exp t)
  have hf1 := einastoMetricSecondJet_hasDerivAt d l einastoGaussianShape t
  have hR1 := einastoGaussianRicciSlope_hasDerivAt d l (exp t)
  have h := (((((hR.const_mul 2).mul hD).add (((hR.pow 2).const_mul σ).div_const (16 * Real.pi))).sub
    ((hf.mul hR2).div_const (4 * Real.pi))).sub ((hf.mul hS).div_const (2 * Real.pi))).sub
    ((hf1.mul hR1).div_const (8 * Real.pi))
  simp only [Pi.mul_def, Pi.add_def, Pi.sub_def, Pi.pow_apply] at h
  apply h.congr_deriv
  unfold einastoGaussianSourceSlope
  ring

theorem einastoGaussianSourceSlope_continuous (d l σ : ℝ) : Continuous (einastoGaussianSourceSlope d l σ) := by
  have hR := einastoGaussianRicci_continuous d l
  have hD := einastoDensity_continuous d l einastoGaussianShape
  have hD1 := einastoGaussianDensitySlope_continuous d l
  have hf := einastoMetric_continuous d l einastoGaussianShape
  have hR1 := einastoGaussianRicciSlope_continuous d l
  have hR2 := einastoGaussianRicciSecond_continuous d l
  have hR3 := einastoGaussianRicciThird_continuous d l
  have hS := einastoGaussianRicciQuotient_continuous d l
  have hS1 := einastoGaussianRicciQuotientSlope_continuous d l
  have hf1 := einastoMetricFirstJet_continuous d l einastoGaussianShape
  have hf2 := einastoMetricSecondJet_continuous d l einastoGaussianShape
  unfold einastoGaussianSourceSlope
  fun_prop

/-- A finite source remains after the derivative-pole cancellation. -/
theorem einastoGaussianSource_core (d l σ : ℝ) :
    einastoGaussianSource d l σ 0 = -72 * exp d / exp l ^ (2 : ℕ) + 64 * Real.pi * (σ - 1) * exp d ^ (2 : ℕ) := by
  unfold einastoGaussianSource
  rw [einastoGaussianRicci_core, einastoDensity_zero, einastoMetric_zero,
    einastoGaussianRicciSecond_core, einastoGaussianRicciQuotient_core,
    einastoMetricFirstJet_core, einastoGaussianRicciSlope_core]
  field_simp
  ring

theorem einastoGaussianSourceSlope_core (d l σ : ℝ) : einastoGaussianSourceSlope d l σ 0 = 0 := by
  unfold einastoGaussianSourceSlope
  rw [einastoGaussianRicciSlope_core, einastoGaussianDensitySlope_core,
    einastoMetricFirstJet_core, einastoGaussianRicciThird_core,
    einastoGaussianRicciQuotientSlope_core]
  ring

/-- The actual radial source has a finite limit for the Gaussian halo, for either algebraic sign. -/
theorem einastoGaussianSource_core_limit (d l σ : ℝ) :
    Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l einastoGaussianShape) (exp t)) atBot
      (𝓝 (-72 * exp d / exp l ^ (2 : ℕ) + 64 * Real.pi * (σ - 1) * exp d ^ (2 : ℕ))) := by
  have he : (fun t => quadraticRadialSource σ (einastoMetric d l einastoGaussianShape) (exp t)) =
      (fun t => einastoGaussianSource d l σ (exp t)) := by
    funext t
    exact einastoGaussianSource_actual d l σ t
  rw [he, ← einastoGaussianSource_core d l σ]
  exact (einastoGaussianSource_continuous d l σ).continuousAt.tendsto.comp tendsto_exp_atBot

/-- The derivative itself tends to zero; boundedness needed for the curvature correction is proved. -/
theorem einastoGaussianSourceSlope_core_limit (d l σ : ℝ) :
    Tendsto (fun t => deriv (einastoGaussianSource d l σ) (exp t)) atBot (𝓝 0) := by
  have he : (fun t => deriv (einastoGaussianSource d l σ) (exp t)) =
      (fun t => einastoGaussianSourceSlope d l σ (exp t)) := by
    funext t
    exact (einastoGaussianSource_hasDerivAt d l σ t).deriv
  rw [he, ← einastoGaussianSourceSlope_core d l σ]
  exact (einastoGaussianSourceSlope_continuous d l σ).continuousAt.tendsto.comp tendsto_exp_atBot

/-- The regular extension also matches the literal appendix source near the center. -/
theorem einastoGaussianSource_appendix_eventually (d l : ℝ) :
    (fun t => quadraticAppendixSource (einastoMetric d l einastoGaussianShape) (exp t)) =ᶠ[atBot]
      (fun t => einastoGaussianSource d l (-1) (exp t)) := by
  filter_upwards [quadraticAppendixSource_einasto_all_shapes_eventually d l einastoGaussianShape] with t ht
  rw [ht, einastoGaussianSource_actual]

end GaloisForLFunctions.HTGeometry
