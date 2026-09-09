import GaloisForLFunctions.HTGeometry.EinastoMetricJetExtensions

/-!
# Actual curvature derivatives for every Einasto shape

Generalize the two explicit profiles used in the audit of arXiv:2608.23600.
The positive shape exponent is q=exp(-a); its radial profile variable is
u=(r/exp(l))^q. The actual first and second Ricci derivatives factor through
u/r and u/r². These exact identities expose the regularity threshold without
assuming bounded curvature derivatives or solving a numerical field equation.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Dimensionless Einasto profile variable; its exponent is always positive. -/
def einastoProfilePower (l a r : ℝ) : ℝ := (r / exp l) ^ exp (-a)

def einastoShapeRicci (d l a r : ℝ) : ℝ :=
  8 * Real.pi * einastoDensity d l a r * (exp (-a) * einastoProfilePower l a r - 4)

def einastoShapeRicciSlope (d l a r : ℝ) : ℝ :=
  8 * Real.pi * exp (-a) * einastoDensity d l a r * einastoProfilePower l a r / r *
    (exp (-a) + 4 - exp (-a) * einastoProfilePower l a r)

def einastoShapeRicciSecond (d l a r : ℝ) : ℝ :=
  8 * Real.pi * exp (-a) * einastoDensity d l a r * einastoProfilePower l a r / r ^ 2 *
    ((exp (-a) - 1) * (exp (-a) + 4) -
      exp (-a) * (3 * exp (-a) + 3) * einastoProfilePower l a r +
      exp (-a) ^ 2 * einastoProfilePower l a r ^ 2)

theorem einastoProfilePower_continuous (l a : ℝ) : Continuous (einastoProfilePower l a) :=
  (continuous_rpow_const (exp_pos (-a)).le).comp (continuous_id.div_const (exp l))

theorem einastoProfilePower_zero (l a : ℝ) : einastoProfilePower l a 0 = 0 := by
  simp [einastoProfilePower, Real.zero_rpow (exp_ne_zero (-a))]

theorem einastoProfilePower_pos (l a t : ℝ) : 0 < einastoProfilePower l a (exp t) := by
  unfold einastoProfilePower
  positivity

theorem einastoProfilePower_exp (l a t : ℝ) :
    einastoProfilePower l a (exp t) = exp (exp (-a) * (t - l)) := by
  unfold einastoProfilePower
  rw [← exp_sub, ← Real.exp_mul]
  congr 1
  ring

theorem einastoProfilePower_hasDerivAt (l a t : ℝ) :
    HasDerivAt (einastoProfilePower l a)
      (exp (-a) * einastoProfilePower l a (exp t) / exp t) (exp t) := by
  have hp : 0 < exp t / exp l := by positivity
  have h := (hasDerivAt_rpow_const (p := exp (-a)) (Or.inl hp.ne')).comp (exp t)
    ((hasDerivAt_id (exp t)).div_const (exp l))
  apply h.congr_deriv
  dsimp [einastoProfilePower]
  rw [rpow_sub hp, rpow_one]
  field_simp

/-- A continuous extension of the actual Ricci scalar, for every positive shape exponent. -/
theorem einastoShapeRicci_actual (d l a t : ℝ) :
    radialRicciScalar (einastoMetric d l a) (exp t) = einastoShapeRicci d l a (exp t) := by
  rw [radialRicciScalar_einasto, einastoRadialRicci_eq]
  unfold einastoShapeRicci einastoProfilePower einastoSlope
  ring

theorem einastoShapeRicci_continuous (d l a : ℝ) : Continuous (einastoShapeRicci d l a) := by
  have hD := einastoDensity_continuous d l a
  have hU := einastoProfilePower_continuous l a
  unfold einastoShapeRicci
  fun_prop

theorem einastoShapeRicci_core (d l a : ℝ) : einastoShapeRicci d l a 0 = -32 * Real.pi * exp d := by
  rw [einastoShapeRicci, einastoProfilePower_zero, einastoDensity_zero]
  ring

theorem einastoShapeRicci_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (einastoShapeRicci d l a) (einastoShapeRicciSlope d l a (exp t)) (exp t) := by
  have h := ((einastoDensity_derivative d l a t).const_mul (8 * Real.pi)).mul
    (((einastoProfilePower_hasDerivAt l a t).const_mul (exp (-a))).sub_const 4)
  simp only [Pi.mul_def] at h
  apply h.congr_deriv
  unfold einastoShapeRicciSlope einastoSlope einastoProfilePower
  field_simp
  ring

theorem einastoShapeRicciSlope_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (einastoShapeRicciSlope d l a) (einastoShapeRicciSecond d l a (exp t)) (exp t) := by
  have hU := einastoProfilePower_hasDerivAt l a t
  have hD := einastoDensity_derivative d l a t
  have hn := ((hD.const_mul (8 * Real.pi * exp (-a))).mul hU).div
    (hasDerivAt_id (exp t)) (exp_ne_zero t)
  have h := hn.mul ((hU.const_mul (exp (-a))).const_sub (exp (-a) + 4))
  simp only [Pi.mul_def, Pi.div_def, id_eq] at h
  apply h.congr_deriv
  unfold einastoShapeRicciSecond einastoSlope einastoProfilePower
  field_simp
  ring

/-- The differentiated expression agrees with the metric's actual Ricci derivative. -/
theorem einastoShapeRicci_actual_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (radialRicciScalar (einastoMetric d l a))
      (einastoShapeRicciSlope d l a (exp t)) (exp t) := by
  apply (einastoShapeRicci_hasDerivAt d l a t).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have h := einastoShapeRicci_actual d l a (log r)
  simpa only [exp_log hr] using h

theorem einastoShapeRicci_actual_derivative (d l a t : ℝ) :
    deriv (radialRicciScalar (einastoMetric d l a)) (exp t) = einastoShapeRicciSlope d l a (exp t) :=
  (einastoShapeRicci_actual_hasDerivAt d l a t).deriv

/-- The second derivative is derived from actual curvature, not supplied as profile data. -/
theorem einastoShapeRicci_actual_second_derivative (d l a t : ℝ) :
    deriv (deriv (radialRicciScalar (einastoMetric d l a))) (exp t) = einastoShapeRicciSecond d l a (exp t) := by
  have h : HasDerivAt (deriv (radialRicciScalar (einastoMetric d l a)))
      (einastoShapeRicciSecond d l a (exp t)) (exp t) := by
    apply (einastoShapeRicciSlope_hasDerivAt d l a t).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
    have h := einastoShapeRicci_actual_derivative d l a (log r)
    simpa only [exp_log hr] using h
  exact h.deriv

end GaloisForLFunctions.HTGeometry
