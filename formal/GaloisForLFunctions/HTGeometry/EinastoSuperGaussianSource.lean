import GaloisForLFunctions.HTGeometry.EinastoShapeEulerDerivative
import GaloisForLFunctions.HTGeometry.EinastoShapeNonuniformCore

/-!
# Actual super-Gaussian sources and the weighted derivative needed for curvature

For every q=2+exp(s)>2, construct a continuous extension of the actual
quadratic source through the center. Its derivative need not be bounded, so
prove the exact weighted derivative instead. The extension of r E'(r) is
continuous and vanishes at zero. This supplies the Green inverse's full
second-derivative input, including exponents between two and three.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem einastoSuperGaussianShape_exponent (s : ℝ) :
    exp (-einastoSuperGaussianShape s) = 2 + exp s := by
  unfold einastoSuperGaussianShape
  rw [neg_neg, exp_log (by positivity : 0 < 2 + exp s)]

/-- Exact radial power left after taking two curvature derivatives. -/
def einastoSuperGaussianWeight (l s r : ℝ) : ℝ := exp (-(2 + exp s) * l) * r ^ exp s

/-- Continuous extension of the actual super-Gaussian radial source. -/
def einastoSuperGaussianSource (d l s σ r : ℝ) : ℝ :=
  einastoSuperGaussianWeight l s r * einastoShapeSourceFactor d l (einastoSuperGaussianShape s) r +
    einastoShapeSourceDefect d l (einastoSuperGaussianShape s) σ r

/-- Continuous extension of r times the actual source derivative. -/
def einastoSuperGaussianSourceEuler (d l s σ r : ℝ) : ℝ :=
  einastoSuperGaussianWeight l s r *
    (exp s * einastoShapeSourceFactor d l (einastoSuperGaussianShape s) r +
      einastoShapeSourceFactorEuler d l (einastoSuperGaussianShape s) r) +
    einastoShapeSourceDefectEuler d l (einastoSuperGaussianShape s) σ r

theorem einastoSuperGaussianWeight_continuous (l s : ℝ) : Continuous (einastoSuperGaussianWeight l s) :=
  continuous_const.mul (continuous_rpow_const (exp_pos s).le)

theorem einastoSuperGaussianWeight_zero (l s : ℝ) : einastoSuperGaussianWeight l s 0 = 0 := by
  simp only [einastoSuperGaussianWeight, Real.zero_rpow (exp_ne_zero s), mul_zero]

theorem einastoSuperGaussianWeight_actual (l s t : ℝ) :
    einastoProfilePower l (einastoSuperGaussianShape s) (exp t) / exp t ^ 2 =
      einastoSuperGaussianWeight l s (exp t) := by
  rw [einastoProfilePower_scaled_exp, einastoSuperGaussianShape_exponent]
  unfold einastoSuperGaussianWeight
  rw [← Real.exp_mul, ← exp_add]
  congr 1
  ring

theorem einastoSuperGaussianWeight_hasDerivAt (l s t : ℝ) :
    HasDerivAt (einastoSuperGaussianWeight l s)
      (exp s * einastoSuperGaussianWeight l s (exp t) / exp t) (exp t) := by
  have h := (hasDerivAt_rpow_const (p := exp s) (Or.inl (exp_ne_zero t))).const_mul (exp (-(2 + exp s) * l))
  apply h.congr_deriv
  unfold einastoSuperGaussianWeight
  rw [rpow_sub (exp_pos t), rpow_one]
  ring

/-- The extension equals the source obtained from actual metric and curvature derivatives. -/
theorem einastoSuperGaussianSource_actual (d l s σ t : ℝ) :
    quadraticRadialSource σ (einastoMetric d l (einastoSuperGaussianShape s)) (exp t) =
      einastoSuperGaussianSource d l s σ (exp t) := by
  rw [einastoShapeSource_decomposition, einastoSuperGaussianWeight_actual]
  rfl

theorem einastoSuperGaussianSource_continuous (d l s σ : ℝ) : Continuous (einastoSuperGaussianSource d l s σ) :=
  ((einastoSuperGaussianWeight_continuous l s).mul
    (einastoShapeSourceFactor_continuous d l (einastoSuperGaussianShape s))).add
    (einastoShapeSourceDefect_continuous d l (einastoSuperGaussianShape s) σ)

theorem einastoSuperGaussianSourceEuler_continuous (d l s σ : ℝ) : Continuous (einastoSuperGaussianSourceEuler d l s σ) :=
  ((einastoSuperGaussianWeight_continuous l s).mul
    ((continuous_const.mul (einastoShapeSourceFactor_continuous d l (einastoSuperGaussianShape s))).add
      (einastoShapeSourceFactorEuler_continuous d l (einastoSuperGaussianShape s)))).add
    (einastoShapeSourceDefectEuler_continuous d l (einastoSuperGaussianShape s) σ)

theorem einastoSuperGaussianSource_core (d l s σ : ℝ) :
    einastoSuperGaussianSource d l s σ 0 = 64 * Real.pi * (σ - 1) * exp d ^ 2 := by
  rw [einastoSuperGaussianSource, einastoSuperGaussianWeight_zero, zero_mul, zero_add,
    einastoShapeSourceDefect_core]

theorem einastoSuperGaussianSourceEuler_core (d l s σ : ℝ) : einastoSuperGaussianSourceEuler d l s σ 0 = 0 := by
  rw [einastoSuperGaussianSourceEuler, einastoSuperGaussianWeight_zero, zero_mul, zero_add,
    einastoShapeSourceDefectEuler_core]

theorem einastoSuperGaussianSource_hasDerivAt (d l s σ t : ℝ) :
    HasDerivAt (einastoSuperGaussianSource d l s σ)
      (einastoSuperGaussianSourceEuler d l s σ (exp t) / exp t) (exp t) := by
  have h := ((einastoSuperGaussianWeight_hasDerivAt l s t).mul
    (einastoShapeSourceFactor_hasDerivAt d l (einastoSuperGaussianShape s) t)).add
    (einastoShapeSourceDefect_hasDerivAt d l (einastoSuperGaussianShape s) σ t)
  simp only [Pi.mul_def, Pi.add_def] at h
  apply h.congr_deriv
  unfold einastoSuperGaussianSourceEuler
  ring

/-- Differentiability of the actual radial source follows from the proved extension. -/
theorem einastoSuperGaussianSource_actual_hasDerivAt (d l s σ t : ℝ) :
    HasDerivAt (quadraticRadialSource σ (einastoMetric d l (einastoSuperGaussianShape s)))
      (einastoSuperGaussianSourceEuler d l s σ (exp t) / exp t) (exp t) := by
  apply (einastoSuperGaussianSource_hasDerivAt d l s σ t).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have h := einastoSuperGaussianSource_actual d l s σ (log r)
  simpa only [exp_log hr] using h

/-- Exactly the weighted derivative required for the metric's second derivative tends to zero. -/
theorem einastoSuperGaussianSource_weighted_derivative_limit (d l s σ : ℝ) :
    Tendsto (fun t => exp t * deriv (einastoSuperGaussianSource d l s σ) (exp t)) atBot (𝓝 0) := by
  have he : (fun t => exp t * deriv (einastoSuperGaussianSource d l s σ) (exp t)) =
      (fun t => einastoSuperGaussianSourceEuler d l s σ (exp t)) := by
    funext t
    rw [(einastoSuperGaussianSource_hasDerivAt d l s σ t).deriv]
    field_simp
  rw [he, ← einastoSuperGaussianSourceEuler_core d l s σ]
  exact (einastoSuperGaussianSourceEuler_continuous d l s σ).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoSuperGaussianSource_actual_weighted_derivative_limit (d l s σ : ℝ) :
    Tendsto (fun t => exp t * deriv (quadraticRadialSource σ (einastoMetric d l (einastoSuperGaussianShape s))) (exp t)) atBot (𝓝 0) := by
  have he : (fun t => exp t * deriv (quadraticRadialSource σ (einastoMetric d l (einastoSuperGaussianShape s))) (exp t)) =
      (fun t => einastoSuperGaussianSourceEuler d l s σ (exp t)) := by
    funext t
    rw [(einastoSuperGaussianSource_actual_hasDerivAt d l s σ t).deriv]
    field_simp
  rw [he, ← einastoSuperGaussianSourceEuler_core d l s σ]
  exact (einastoSuperGaussianSourceEuler_continuous d l s σ).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoSuperGaussianSource_appendix_eventually (d l s : ℝ) :
    (fun t => quadraticAppendixSource (einastoMetric d l (einastoSuperGaussianShape s)) (exp t)) =ᶠ[atBot]
      (fun t => einastoSuperGaussianSource d l s (-1) (exp t)) := by
  filter_upwards [quadraticAppendixSource_einasto_all_shapes_eventually d l (einastoSuperGaussianShape s)] with t ht
  rw [ht, einastoSuperGaussianSource_actual]

end GaloisForLFunctions.HTGeometry
