import GaloisForLFunctions.HTGeometry.EinastoMetricJetExtensions

/-!
# Actual Gaussian Einasto curvature and its smooth source data

At shape α=1/2 in arXiv:2608.23600, the corpus's logarithmic shape parameter
is -log 2. The density becomes Gaussian. Its actual scalar curvature derivative
vanishes linearly at the center, in contrast to the exponential profile.
The divided derivative R'/r has a smooth explicit extension. All derivatives
below are proved from the actual Gaussian density and identified with the
metric curvature on the positive ray; no independent curvature jets are assumed.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoGaussianShape : ℝ := -log 2

theorem einastoGaussianShape_exponent : exp (-einastoGaussianShape) = 2 := by
  unfold einastoGaussianShape
  rw [neg_neg, exp_log (by norm_num : (0 : ℝ) < 2)]

theorem einastoDensity_gaussian (d l r : ℝ) :
    einastoDensity d l einastoGaussianShape r = exp d * exp (-((r / exp l) ^ 2)) := by
  unfold einastoDensity
  rw [einastoGaussianShape_exponent, Real.rpow_two]

def einastoGaussianDensitySlope (d l r : ℝ) : ℝ :=
  -2 * r / exp l ^ 2 * einastoDensity d l einastoGaussianShape r

def einastoGaussianRicci (d l r : ℝ) : ℝ :=
  8 * Real.pi * einastoDensity d l einastoGaussianShape r * (2 * (r / exp l) ^ 2 - 4)

/-- Smooth extension of the crucial quotient R'/r. -/
def einastoGaussianRicciSlopeQuotient (d l r : ℝ) : ℝ :=
  32 * Real.pi * einastoDensity d l einastoGaussianShape r / exp l ^ 2 * (3 - (r / exp l) ^ 2)

def einastoGaussianRicciSlope (d l r : ℝ) : ℝ := r * einastoGaussianRicciSlopeQuotient d l r

def einastoGaussianRicciQuotientSlope (d l r : ℝ) : ℝ :=
  64 * Real.pi * einastoDensity d l einastoGaussianShape r / exp l ^ 3 *
    (r / exp l) * ((r / exp l) ^ 2 - 4)

def einastoGaussianRicciSecond (d l r : ℝ) : ℝ :=
  32 * Real.pi * einastoDensity d l einastoGaussianShape r / exp l ^ 2 *
    (2 * (r / exp l) ^ 4 - 9 * (r / exp l) ^ 2 + 3)

def einastoGaussianRicciThird (d l r : ℝ) : ℝ :=
  32 * Real.pi * einastoDensity d l einastoGaussianShape r / exp l ^ 3 *
    (-4 * (r / exp l) ^ 5 + 26 * (r / exp l) ^ 3 - 24 * (r / exp l))

theorem einastoDensity_gaussian_hasDerivAt (d l r : ℝ) :
    HasDerivAt (einastoDensity d l einastoGaussianShape) (einastoGaussianDensitySlope d l r) r := by
  have he : einastoDensity d l einastoGaussianShape = fun s => exp d * exp (-((s / exp l) ^ 2)) := by
    funext s
    exact einastoDensity_gaussian d l s
  rw [he]
  have h := (((((hasDerivAt_id r).div_const (exp l)).pow 2).neg).exp).const_mul (exp d)
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  unfold einastoGaussianDensitySlope
  rw [einastoDensity_gaussian]
  norm_num only [Nat.cast_ofNat, pow_one]
  field_simp

theorem einastoGaussianRicci_hasDerivAt (d l r : ℝ) :
    HasDerivAt (einastoGaussianRicci d l) (einastoGaussianRicciSlope d l r) r := by
  have h := ((einastoDensity_gaussian_hasDerivAt d l r).const_mul (8 * Real.pi)).mul
    (((((hasDerivAt_id r).div_const (exp l)).pow 2).const_mul 2).sub_const 4)
  simp only [Pi.mul_def, Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  unfold einastoGaussianDensitySlope einastoGaussianRicciSlope einastoGaussianRicciSlopeQuotient
  norm_num only [Nat.cast_ofNat, pow_one]
  field_simp
  ring

theorem einastoGaussianRicciQuotient_hasDerivAt (d l r : ℝ) :
    HasDerivAt (einastoGaussianRicciSlopeQuotient d l) (einastoGaussianRicciQuotientSlope d l r) r := by
  have h := (((einastoDensity_gaussian_hasDerivAt d l r).const_mul (32 * Real.pi)).div_const (exp l ^ 2)).mul
    ((((hasDerivAt_id r).div_const (exp l)).pow 2).const_sub 3)
  simp only [Pi.mul_def, Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  unfold einastoGaussianDensitySlope einastoGaussianRicciQuotientSlope
  norm_num only [Nat.cast_ofNat, pow_one]
  field_simp
  ring

theorem einastoGaussianRicciSlope_hasDerivAt (d l r : ℝ) :
    HasDerivAt (einastoGaussianRicciSlope d l) (einastoGaussianRicciSecond d l r) r := by
  have h := (hasDerivAt_id r).mul (einastoGaussianRicciQuotient_hasDerivAt d l r)
  simp only [Pi.mul_def, id_eq] at h
  apply h.congr_deriv
  unfold einastoGaussianRicciSlopeQuotient einastoGaussianRicciQuotientSlope einastoGaussianRicciSecond
  field_simp
  ring

theorem einastoGaussianRicciSecond_hasDerivAt (d l r : ℝ) :
    HasDerivAt (einastoGaussianRicciSecond d l) (einastoGaussianRicciThird d l r) r := by
  have hq := (hasDerivAt_id r).div_const (exp l)
  have hp := (((hq.pow 4).const_mul 2).sub ((hq.pow 2).const_mul 9)).add_const 3
  have h := (((einastoDensity_gaussian_hasDerivAt d l r).const_mul (32 * Real.pi)).div_const (exp l ^ 2)).mul hp
  simp only [Pi.mul_def, Pi.sub_def, Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  unfold einastoGaussianDensitySlope einastoGaussianRicciThird
  norm_num only [Nat.cast_ofNat, pow_one]
  field_simp
  ring

theorem einastoGaussianRicci_actual (d l t : ℝ) :
    radialRicciScalar (einastoMetric d l einastoGaussianShape) (exp t) = einastoGaussianRicci d l (exp t) := by
  rw [radialRicciScalar_einasto, einastoRadialRicci_eq]
  unfold einastoSlope einastoGaussianRicci
  rw [einastoGaussianShape_exponent, Real.rpow_two]
  ring

theorem einastoGaussianRicci_actual_hasDerivAt (d l t : ℝ) :
    HasDerivAt (radialRicciScalar (einastoMetric d l einastoGaussianShape))
      (einastoGaussianRicciSlope d l (exp t)) (exp t) := by
  apply (einastoGaussianRicci_hasDerivAt d l (exp t)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have h := einastoGaussianRicci_actual d l (log r)
  simpa only [exp_log hr] using h

theorem einastoGaussianRicci_actual_derivative (d l t : ℝ) :
    deriv (radialRicciScalar (einastoMetric d l einastoGaussianShape)) (exp t) =
      einastoGaussianRicciSlope d l (exp t) :=
  (einastoGaussianRicci_actual_hasDerivAt d l t).deriv

theorem einastoGaussianRicci_actual_second_derivative (d l t : ℝ) :
    deriv (deriv (radialRicciScalar (einastoMetric d l einastoGaussianShape))) (exp t) =
      einastoGaussianRicciSecond d l (exp t) := by
  have h : HasDerivAt (deriv (radialRicciScalar (einastoMetric d l einastoGaussianShape)))
      (einastoGaussianRicciSecond d l (exp t)) (exp t) := by
    apply (einastoGaussianRicciSlope_hasDerivAt d l (exp t)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
    have he := einastoGaussianRicci_actual_derivative d l (log r)
    simpa only [exp_log hr] using he
  exact h.deriv

theorem einastoGaussianDensitySlope_continuous (d l : ℝ) : Continuous (einastoGaussianDensitySlope d l) := by
  have h := einastoDensity_continuous d l einastoGaussianShape
  unfold einastoGaussianDensitySlope
  fun_prop

theorem einastoGaussianRicci_continuous (d l : ℝ) : Continuous (einastoGaussianRicci d l) := by
  have h := einastoDensity_continuous d l einastoGaussianShape
  unfold einastoGaussianRicci
  fun_prop

theorem einastoGaussianRicciQuotient_continuous (d l : ℝ) : Continuous (einastoGaussianRicciSlopeQuotient d l) := by
  have h := einastoDensity_continuous d l einastoGaussianShape
  unfold einastoGaussianRicciSlopeQuotient
  fun_prop

theorem einastoGaussianRicciSlope_continuous (d l : ℝ) : Continuous (einastoGaussianRicciSlope d l) :=
  continuous_id.mul (einastoGaussianRicciQuotient_continuous d l)

theorem einastoGaussianRicciQuotientSlope_continuous (d l : ℝ) : Continuous (einastoGaussianRicciQuotientSlope d l) := by
  have h := einastoDensity_continuous d l einastoGaussianShape
  unfold einastoGaussianRicciQuotientSlope
  fun_prop

theorem einastoGaussianRicciSecond_continuous (d l : ℝ) : Continuous (einastoGaussianRicciSecond d l) := by
  have h := einastoDensity_continuous d l einastoGaussianShape
  unfold einastoGaussianRicciSecond
  fun_prop

theorem einastoGaussianRicciThird_continuous (d l : ℝ) : Continuous (einastoGaussianRicciThird d l) := by
  have h := einastoDensity_continuous d l einastoGaussianShape
  unfold einastoGaussianRicciThird
  fun_prop

theorem einastoGaussianDensitySlope_core (d l : ℝ) : einastoGaussianDensitySlope d l 0 = 0 := by
  unfold einastoGaussianDensitySlope
  ring

theorem einastoGaussianRicci_core (d l : ℝ) : einastoGaussianRicci d l 0 = -32 * Real.pi * exp d := by
  unfold einastoGaussianRicci
  rw [einastoDensity_zero]
  ring

theorem einastoGaussianRicciQuotient_core (d l : ℝ) :
    einastoGaussianRicciSlopeQuotient d l 0 = 96 * Real.pi * exp d / exp l ^ 2 := by
  unfold einastoGaussianRicciSlopeQuotient
  rw [einastoDensity_zero]
  ring

theorem einastoGaussianRicciSlope_core (d l : ℝ) : einastoGaussianRicciSlope d l 0 = 0 := by
  unfold einastoGaussianRicciSlope
  ring

theorem einastoGaussianRicciQuotientSlope_core (d l : ℝ) : einastoGaussianRicciQuotientSlope d l 0 = 0 := by
  unfold einastoGaussianRicciQuotientSlope
  ring

theorem einastoGaussianRicciSecond_core (d l : ℝ) :
    einastoGaussianRicciSecond d l 0 = 96 * Real.pi * exp d / exp l ^ 2 := by
  unfold einastoGaussianRicciSecond
  rw [einastoDensity_zero]
  ring

theorem einastoGaussianRicciThird_core (d l : ℝ) : einastoGaussianRicciThird d l 0 = 0 := by
  unfold einastoGaussianRicciThird
  ring

end GaloisForLFunctions.HTGeometry
