import GaloisForLFunctions.RHTower.XiMassTwoRapidityStationaryPhase

/-!
# Timelike saddle polarity of the literal two-rapidity covariance

The literal mass covariance separates into one rapidity phase minus another.  At every timelike
stationary pair its two directional second derivatives have opposite strict signs.  Thus the
two-dimensional stationary cell is a nondegenerate saddle of signature zero, so stationary-phase
geometry itself supplies no one-sided Maslov sign for the unresolved Route-T covariance bound.

The result does not bound that covariance.  It identifies the remaining required cancellation as
an arithmetic relation between cofinal prime-frequency cells.
-/

namespace RHTower

noncomputable section

/-- First rapidity derivative of the two-rapidity phase. -/
def xiMassTwoRapidityCorrelationLeftVelocity (u h t : ℝ) : ℝ :=
  u * Real.sinh t + h * Real.cosh t

/-- Second derivative in the first rapidity direction. -/
def xiMassTwoRapidityCorrelationLeftCurvature (u h t : ℝ) : ℝ :=
  u * Real.cosh t + h * Real.sinh t

/-- Second derivative in the second rapidity direction. -/
def xiMassTwoRapidityCorrelationRightCurvature (u k s : ℝ) : ℝ :=
  -(u * Real.cosh s + k * Real.sinh s)

/-- The literal covariance amplitude has strictly positive real part everywhere. -/
theorem xiMassTwoRapidityCorrelationAmplitude_re_pos
    (a sigma t s : ℝ) :
    0 < (xiMassTwoRapidityCorrelationAmplitude a sigma t s).re := by
  unfold xiMassTwoRapidityCorrelationAmplitude
  change 0 < Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t) *
    Real.cosh s * Real.exp (-(a * sigma) * Real.cosh s)
  positivity

/-- The literal covariance amplitude has no imaginary phase. -/
theorem xiMassTwoRapidityCorrelationAmplitude_im_eq_zero
    (a sigma t s : ℝ) :
    (xiMassTwoRapidityCorrelationAmplitude a sigma t s).im = 0 := by
  unfold xiMassTwoRapidityCorrelationAmplitude
  rfl

/-- The first rapidity derivative of the literal correlation phase. -/
theorem deriv_xiMassTwoRapidityCorrelationPhase_left (u h k s t : ℝ) :
    deriv (fun x : ℝ => xiMassTwoRapidityCorrelationPhase u h k x s) t =
      xiMassTwoRapidityCorrelationLeftVelocity u h t := by
  unfold xiMassTwoRapidityCorrelationPhase xiMassTwoRapidityCorrelationLeftVelocity
  change deriv (((fun x : ℝ => u * Real.cosh x) + (fun x : ℝ => h * Real.sinh x)) -
      fun _ : ℝ => u * Real.cosh s + k * Real.sinh s) t = _
  have hcosh : DifferentiableAt ℝ (fun x : ℝ => u * Real.cosh x) t :=
    (Real.differentiable_cosh.differentiableAt).const_mul u
  have hsinh : DifferentiableAt ℝ (fun x : ℝ => h * Real.sinh x) t :=
    (Real.differentiable_sinh.differentiableAt).const_mul h
  have hconst : DifferentiableAt ℝ
      (fun _ : ℝ => u * Real.cosh s + k * Real.sinh s) t := differentiableAt_const _
  rw [deriv_sub (hcosh.add hsinh) hconst, deriv_add hcosh hsinh,
    deriv_const_mul_field, Real.deriv_cosh,
    deriv_const_mul_field, Real.deriv_sinh, deriv_const]
  ring

/-- The second rapidity derivative of the literal correlation phase. -/
theorem deriv_xiMassTwoRapidityCorrelationPhase_right (u h k t s : ℝ) :
    deriv (fun x : ℝ => xiMassTwoRapidityCorrelationPhase u h k t x) s =
      -(u * Real.sinh s + k * Real.cosh s) := by
  unfold xiMassTwoRapidityCorrelationPhase
  change deriv ((fun _ : ℝ => u * Real.cosh t + h * Real.sinh t) -
      ((fun x : ℝ => u * Real.cosh x) + (fun x : ℝ => k * Real.sinh x))) s = _
  have hcosh : DifferentiableAt ℝ (fun x : ℝ => u * Real.cosh x) s :=
    (Real.differentiable_cosh.differentiableAt).const_mul u
  have hsinh : DifferentiableAt ℝ (fun x : ℝ => k * Real.sinh x) s :=
    (Real.differentiable_sinh.differentiableAt).const_mul k
  have hconst : DifferentiableAt ℝ
      (fun _ : ℝ => u * Real.cosh t + h * Real.sinh t) s := differentiableAt_const _
  rw [deriv_sub hconst (hcosh.add hsinh), deriv_const,
    deriv_add hcosh hsinh, deriv_const_mul_field, Real.deriv_cosh,
    deriv_const_mul_field, Real.deriv_sinh]
  ring

/-- The derivative of the first rapidity velocity is its curvature. -/
theorem deriv_xiMassTwoRapidityCorrelationLeftVelocity (u h t : ℝ) :
    deriv (fun x : ℝ => xiMassTwoRapidityCorrelationLeftVelocity u h x) t =
      xiMassTwoRapidityCorrelationLeftCurvature u h t := by
  unfold xiMassTwoRapidityCorrelationLeftVelocity xiMassTwoRapidityCorrelationLeftCurvature
  change deriv ((fun x : ℝ => u * Real.sinh x) + (fun x : ℝ => h * Real.cosh x)) t = _
  have hsinh : DifferentiableAt ℝ (fun x : ℝ => u * Real.sinh x) t :=
    (Real.differentiable_sinh.differentiableAt).const_mul u
  have hcosh : DifferentiableAt ℝ (fun x : ℝ => h * Real.cosh x) t :=
    (Real.differentiable_cosh.differentiableAt).const_mul h
  rw [deriv_add hsinh hcosh, deriv_const_mul_field, Real.deriv_sinh,
    deriv_const_mul_field, Real.deriv_cosh]

/-- The derivative of the second rapidity velocity is its curvature. -/
theorem deriv_xiMassTwoRapidityCorrelationPhase_right_velocity (u k s : ℝ) :
    deriv (fun x : ℝ => -(u * Real.sinh x + k * Real.cosh x)) s =
      xiMassTwoRapidityCorrelationRightCurvature u k s := by
  unfold xiMassTwoRapidityCorrelationRightCurvature
  have hneg : (fun x : ℝ => -(u * Real.sinh x + k * Real.cosh x)) =
      (fun x : ℝ => (0 : ℝ) - (u * Real.sinh x + k * Real.cosh x)) := by
    funext x
    ring
  rw [hneg]
  change deriv ((fun _ : ℝ => 0) -
      ((fun x : ℝ => u * Real.sinh x) + (fun x : ℝ => k * Real.cosh x))) s = _
  have hsinh : DifferentiableAt ℝ (fun x : ℝ => u * Real.sinh x) s :=
    (Real.differentiable_sinh.differentiableAt).const_mul u
  have hcosh : DifferentiableAt ℝ (fun x : ℝ => k * Real.cosh x) s :=
    (Real.differentiable_cosh.differentiableAt).const_mul k
  have hconst : DifferentiableAt ℝ (fun _ : ℝ => (0 : ℝ)) s := differentiableAt_const _
  rw [deriv_sub hconst (hsinh.add hcosh), deriv_const,
    deriv_add hsinh hcosh, deriv_const_mul_field, Real.deriv_sinh,
    deriv_const_mul_field, Real.deriv_cosh]
  ring

/-- A literal timelike stationary pair has strictly opposite rapidity curvatures. -/
theorem xiMassTwoRapidityCorrelation_timelike_stationary_curvature_sign
    {u h k : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hhu : h < u) (hku : k < u) :
    0 < xiMassTwoRapidityCorrelationLeftCurvature u h (-timelikeRapidity u h) ∧
      xiMassTwoRapidityCorrelationRightCurvature u k (-timelikeRapidity u k) < 0 := by
  constructor
  · unfold xiMassTwoRapidityCorrelationLeftCurvature
    rw [massPhase_timelike hu hh hhu (-timelikeRapidity u h)]
    simpa using mul_pos (Real.sqrt_pos.2 (by nlinarith : 0 < u ^ 2 - h ^ 2))
      (Real.cosh_pos 0)
  · unfold xiMassTwoRapidityCorrelationRightCurvature
    rw [massPhase_timelike hu hk hku (-timelikeRapidity u k)]
    simpa using neg_lt_zero.mpr
      (mul_pos (Real.sqrt_pos.2 (by nlinarith : 0 < u ^ 2 - k ^ 2)) (Real.cosh_pos 0))

/-- The timelike stationary Hessian determinant is strictly negative. -/
theorem xiMassTwoRapidityCorrelation_timelike_stationary_curvature_product_neg
    {u h k : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hhu : h < u) (hku : k < u) :
    xiMassTwoRapidityCorrelationLeftCurvature u h (-timelikeRapidity u h) *
      xiMassTwoRapidityCorrelationRightCurvature u k (-timelikeRapidity u k) < 0 := by
  exact mul_neg_of_pos_of_neg
    (xiMassTwoRapidityCorrelation_timelike_stationary_curvature_sign hu hh hk hhu hku).1
    (xiMassTwoRapidityCorrelation_timelike_stationary_curvature_sign hu hh hk hhu hku).2

end

end RHTower
