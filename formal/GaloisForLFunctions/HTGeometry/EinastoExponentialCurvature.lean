import GaloisForLFunctions.HTGeometry.EinastoQuadraticSignDefect

/-!
# Actual curvature derivatives for the exponential Einasto profile

Specialize the shape index in arXiv:2608.23600 to α=1 (the corpus parameter
is its logarithm, a=0). The density and the positive-radius Ricci scalar have
smooth exponential extensions through zero. The first two derivatives of
that extension are identified with derivatives of the actual metric curvature,
not introduced as independent jet parameters.
-/
noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem einastoDensity_exponential (d l r : ℝ) :
    einastoDensity d l 0 r = Real.exp d * Real.exp (-r / Real.exp l) := by
  simp only [einastoDensity, neg_zero, Real.exp_zero, Real.rpow_one, neg_div]

theorem einastoDensity_exponential_hasDerivAt (d l r : ℝ) :
    HasDerivAt (einastoDensity d l 0) (-einastoDensity d l 0 r / Real.exp l) r := by
  have he : einastoDensity d l 0 = fun s => Real.exp d * Real.exp (-s / Real.exp l) := by
    funext s
    exact einastoDensity_exponential d l s
  rw [he]
  have h := (((hasDerivAt_id r).neg.div_const (Real.exp l)).exp).const_mul (Real.exp d)
  simp only [Pi.neg_apply, id_eq] at h
  apply h.congr_deriv
  ring

/-- Smooth extension of the actual scalar curvature on the positive ray. -/
def einastoExponentialRicci (d l r : ℝ) : ℝ :=
  8 * Real.pi * einastoDensity d l 0 r * (r / Real.exp l - 4)

/-- Explicit first derivative of the extension. -/
def einastoExponentialRicciSlope (d l r : ℝ) : ℝ :=
  8 * Real.pi * einastoDensity d l 0 r / Real.exp l * (5 - r / Real.exp l)

/-- Explicit second derivative of the extension. -/
def einastoExponentialRicciSecond (d l r : ℝ) : ℝ :=
  8 * Real.pi * einastoDensity d l 0 r / Real.exp l ^ 2 * (r / Real.exp l - 6)

/-- A continuous extension of the actual metric derivative through its regular center. -/
def einastoExponentialMetricSlope (d l r : ℝ) : ℝ :=
  r * (2 * einastoCore d l 0 r - 8 * Real.pi * einastoDensity d l 0 r)

theorem einastoExponentialRicci_hasDerivAt (d l r : ℝ) :
    HasDerivAt (einastoExponentialRicci d l) (einastoExponentialRicciSlope d l r) r := by
  have h := ((einastoDensity_exponential_hasDerivAt d l r).const_mul (8 * Real.pi)).mul
    (((hasDerivAt_id r).div_const (Real.exp l)).sub_const 4)
  simp only [Pi.mul_def, id_eq] at h
  apply h.congr_deriv
  unfold einastoExponentialRicciSlope
  ring

theorem einastoExponentialRicciSlope_hasDerivAt (d l r : ℝ) :
    HasDerivAt (einastoExponentialRicciSlope d l) (einastoExponentialRicciSecond d l r) r := by
  have h := (((einastoDensity_exponential_hasDerivAt d l r).const_mul (8 * Real.pi)).div_const
    (Real.exp l)).mul (((hasDerivAt_id r).div_const (Real.exp l)).const_sub 5)
  simp only [Pi.mul_def, id_eq] at h
  apply h.congr_deriv
  unfold einastoExponentialRicciSecond
  field_simp
  ring

theorem einastoExponentialRicci_actual (d l t : ℝ) :
    radialRicciScalar (einastoMetric d l 0) (Real.exp t) = einastoExponentialRicci d l (Real.exp t) := by
  rw [radialRicciScalar_einasto, einastoRadialRicci_eq]
  unfold einastoExponentialRicci einastoSlope
  simp only [neg_zero, Real.exp_zero, Real.rpow_one, one_mul]
  ring

/-- Actual curvature derivatives agree with the smooth extension locally at every positive point. -/
theorem einastoExponentialRicci_actual_hasDerivAt (d l t : ℝ) :
    HasDerivAt (radialRicciScalar (einastoMetric d l 0))
      (einastoExponentialRicciSlope d l (Real.exp t)) (Real.exp t) := by
  apply (einastoExponentialRicci_hasDerivAt d l (Real.exp t)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (Real.exp_pos t)] with r hr
  have h := einastoExponentialRicci_actual d l (Real.log r)
  simpa only [Real.exp_log hr] using h

theorem einastoExponentialRicci_actual_derivative (d l t : ℝ) :
    deriv (radialRicciScalar (einastoMetric d l 0)) (Real.exp t) =
      einastoExponentialRicciSlope d l (Real.exp t) :=
  (einastoExponentialRicci_actual_hasDerivAt d l t).deriv

theorem einastoExponentialRicci_actual_second_derivative (d l t : ℝ) :
    deriv (deriv (radialRicciScalar (einastoMetric d l 0))) (Real.exp t) =
      einastoExponentialRicciSecond d l (Real.exp t) := by
  have h : HasDerivAt (deriv (radialRicciScalar (einastoMetric d l 0)))
      (einastoExponentialRicciSecond d l (Real.exp t)) (Real.exp t) := by
    apply (einastoExponentialRicciSlope_hasDerivAt d l (Real.exp t)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (Real.exp_pos t)] with r hr
    have he := einastoExponentialRicci_actual_derivative d l (Real.log r)
    simpa only [Real.exp_log hr] using he
  exact h.deriv

theorem einastoExponentialMetricSlope_actual (d l t : ℝ) :
    deriv (einastoMetric d l 0) (Real.exp t) = einastoExponentialMetricSlope d l (Real.exp t) := by
  rw [(einastoMetric_derivative d l 0 t).deriv, einastoMass_core]
  unfold einastoExponentialMetricSlope
  field_simp

theorem einastoExponentialRicci_continuous (d l : ℝ) : Continuous (einastoExponentialRicci d l) := by
  exact (continuous_const.mul (einastoDensity_continuous d l 0)).mul
    ((continuous_id.div_const (Real.exp l)).sub continuous_const)

theorem einastoExponentialRicciSlope_continuous (d l : ℝ) : Continuous (einastoExponentialRicciSlope d l) := by
  exact ((continuous_const.mul (einastoDensity_continuous d l 0)).div_const (Real.exp l)).mul
    (continuous_const.sub (continuous_id.div_const (Real.exp l)))

theorem einastoExponentialRicciSecond_continuous (d l : ℝ) : Continuous (einastoExponentialRicciSecond d l) := by
  exact ((continuous_const.mul (einastoDensity_continuous d l 0)).div_const (Real.exp l ^ 2)).mul
    ((continuous_id.div_const (Real.exp l)).sub continuous_const)

theorem einastoExponentialMetricSlope_continuous (d l : ℝ) : Continuous (einastoExponentialMetricSlope d l) := by
  exact continuous_id.mul ((continuous_const.mul (einastoCore_continuous d l 0)).sub
    (continuous_const.mul (einastoDensity_continuous d l 0)))

theorem einastoExponentialRicci_core (d l : ℝ) : einastoExponentialRicci d l 0 = -32 * Real.pi * Real.exp d := by
  unfold einastoExponentialRicci
  rw [einastoDensity_zero]
  ring

theorem einastoExponentialRicciSlope_core (d l : ℝ) :
    einastoExponentialRicciSlope d l 0 = 40 * Real.pi * Real.exp d / Real.exp l := by
  unfold einastoExponentialRicciSlope
  rw [einastoDensity_zero]
  ring

theorem einastoExponentialRicciSecond_core (d l : ℝ) :
    einastoExponentialRicciSecond d l 0 = -48 * Real.pi * Real.exp d / Real.exp l ^ 2 := by
  unfold einastoExponentialRicciSecond
  rw [einastoDensity_zero]
  ring

theorem einastoExponentialMetricSlope_core (d l : ℝ) : einastoExponentialMetricSlope d l 0 = 0 := by
  unfold einastoExponentialMetricSlope
  ring

end GaloisForLFunctions.HTGeometry
