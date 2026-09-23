import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceFifthRootCurvature

/-!
# Gaussian deviation form of the fifth-root action curvature numerator

For a reflected completed-source fibre with action `q`, first jet `q₁`, and second jet `q₂`, the
scaled jets of an exactly Gaussian profile are `t q₁ = t² q₂ = 2q`.  Subtracting this profile
defines two shape deviations, and the action fifth-root curvature numerator splits exactly into a
universal Gaussian margin evaluated at the action plus shape-deviation corrections.

The Gaussian margin `24 r² - 8 q r - 20 q² r - 16 q²` with `r = e^q - 1` is nonnegative on the
positive action ray and admits the explicit quartic-order floor
`q⁴ (8/3 + 7q/3 + 5q²/6 + q³/3 + q⁴/24)`.  The floor follows from the quartic Taylor partial sum
of the exponential: the margin is an upward parabola in `r` whose slope at the partial sum is
already nonnegative, and its exact value at the partial sum is the displayed polynomial, whose
coefficients are nonnegative.  The leading coefficient `8/3` is the pure-Gaussian part of the
order-eight coalescence jet of the curvature numerator.

The first shape deviation differentiates to `t q₂ - q₁`, so `t` times its derivative is exactly
the difference of the second and first deviations: the second deviation is determined by the
profile of the first.
-/

open Real

namespace RHTower

noncomputable section

/-- Value of the action fifth-root curvature numerator on an exactly Gaussian profile, as a
function of the accumulated action alone. -/
def thetaCuspFifthRootGaussianActionMargin (q : ℝ) : ℝ :=
  24 * (Real.exp q - 1) ^ (2 : ℕ) - 8 * q * (Real.exp q - 1) -
    20 * q ^ (2 : ℕ) * (Real.exp q - 1) - 16 * q ^ (2 : ℕ)

/-- First shape deviation of a reflected fibre from its Gaussian profile: the scaled first jet
minus twice the action. -/
def thetaCuspReflectedActionShapeDeviationOne (u t : ℝ) : ℝ :=
  t * thetaCuspReflectedLogJetOne u t - 2 * thetaCuspReflectedLogAction u t

/-- Second shape deviation of a reflected fibre from its Gaussian profile: the twice-scaled
second jet minus twice the action. -/
def thetaCuspReflectedActionShapeDeviationTwo (u t : ℝ) : ℝ :=
  t ^ (2 : ℕ) * thetaCuspReflectedLogJetTwo u t - 2 * thetaCuspReflectedLogAction u t

/-- Quartic Taylor partial sum bound for the shifted exponential on the nonnegative ray. -/
private theorem quartic_sum_le_exp_sub_one {q : ℝ} (hq : 0 ≤ q) :
    q + q ^ (2 : ℕ) / 2 + q ^ (3 : ℕ) / 6 + q ^ (4 : ℕ) / 24 ≤ Real.exp q - 1 := by
  have h := Real.sum_le_exp_of_nonneg hq 5
  have hsum : ∑ i ∈ Finset.range 5, q ^ i / i.factorial =
      1 + q + q ^ (2 : ℕ) / 2 + q ^ (3 : ℕ) / 6 + q ^ (4 : ℕ) / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  linarith

/-- **Quartic floor for the Gaussian margin.**  On the nonnegative action ray the Gaussian margin
dominates an explicit nonnegative-coefficient quartic-order polynomial; the leading coefficient
`8/3` is the pure-Gaussian coalescence jet. -/
theorem le_thetaCuspFifthRootGaussianActionMargin {q : ℝ} (hq : 0 ≤ q) :
    q ^ (4 : ℕ) * (8 / 3 + 7 * q / 3 + 5 * q ^ (2 : ℕ) / 6 + q ^ (3 : ℕ) / 3 + q ^ (4 : ℕ) / 24) ≤
      thetaCuspFifthRootGaussianActionMargin q := by
  unfold thetaCuspFifthRootGaussianActionMargin
  have hsE := quartic_sum_le_exp_sub_one hq
  have hcoef : 0 ≤ 24 * ((Real.exp q - 1) + (q + q ^ (2 : ℕ) / 2 + q ^ (3 : ℕ) / 6 + q ^ (4 : ℕ) / 24)) -
      (8 * q + 20 * q ^ (2 : ℕ)) := by
    nlinarith [pow_nonneg hq 3, pow_nonneg hq 4, sq_nonneg q]
  have hprod : 0 ≤ ((Real.exp q - 1) - (q + q ^ (2 : ℕ) / 2 + q ^ (3 : ℕ) / 6 + q ^ (4 : ℕ) / 24)) *
      (24 * ((Real.exp q - 1) + (q + q ^ (2 : ℕ) / 2 + q ^ (3 : ℕ) / 6 + q ^ (4 : ℕ) / 24)) -
        (8 * q + 20 * q ^ (2 : ℕ))) :=
    mul_nonneg (by linarith) hcoef
  nlinarith [hprod]

/-- The Gaussian margin is nonnegative on the nonnegative action ray. -/
theorem thetaCuspFifthRootGaussianActionMargin_nonneg {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ thetaCuspFifthRootGaussianActionMargin q := by
  have hfloor := le_thetaCuspFifthRootGaussianActionMargin hq
  have hpoly : 0 ≤ q ^ (4 : ℕ) * (8 / 3 + 7 * q / 3 + 5 * q ^ (2 : ℕ) / 6 + q ^ (3 : ℕ) / 3 + q ^ (4 : ℕ) / 24) := by
    positivity
  linarith

/-- **Gaussian deviation identity.**  The action fifth-root curvature numerator is the Gaussian
margin at the action, plus a linear gain in the second shape deviation, minus linear and
quadratic corrections in the first shape deviation. -/
theorem thetaCuspReflectedActionFifthRootCurvatureNumerator_eq_gaussianMargin_add_shape
    (u t : ℝ) :
    thetaCuspReflectedActionFifthRootCurvatureNumerator u t =
      thetaCuspFifthRootGaussianActionMargin (thetaCuspReflectedLogAction u t) +
        5 * (Real.exp (thetaCuspReflectedLogAction u t) - 1) *
          thetaCuspReflectedActionShapeDeviationTwo u t -
        (9 * (Real.exp (thetaCuspReflectedLogAction u t) - 1) +
          16 * thetaCuspReflectedLogAction u t +
          20 * thetaCuspReflectedLogAction u t *
            (Real.exp (thetaCuspReflectedLogAction u t) - 1)) *
          thetaCuspReflectedActionShapeDeviationOne u t -
        (4 + 5 * (Real.exp (thetaCuspReflectedLogAction u t) - 1)) *
          thetaCuspReflectedActionShapeDeviationOne u t ^ (2 : ℕ) := by
  unfold thetaCuspReflectedActionFifthRootCurvatureNumerator
    thetaCuspFifthRootGaussianActionMargin
    thetaCuspReflectedActionShapeDeviationOne
    thetaCuspReflectedActionShapeDeviationTwo
  ring

/-- The first shape deviation differentiates to `t q₂ - q₁`. -/
theorem hasDerivAt_thetaCuspReflectedActionShapeDeviationOne (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedActionShapeDeviationOne u)
      (t * thetaCuspReflectedLogJetTwo u t - thetaCuspReflectedLogJetOne u t) t := by
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h1 : HasDerivAt (fun s : ℝ => s * thetaCuspReflectedLogJetOne u s)
      (1 * thetaCuspReflectedLogJetOne u t +
        t * thetaCuspReflectedLogJetTwo u t) t :=
    hid.mul (hasDerivAt_thetaCuspReflectedLogJetOne u t)
  have h2 : HasDerivAt (fun s : ℝ => 2 * thetaCuspReflectedLogAction u s)
      (2 * thetaCuspReflectedLogJetOne u t) t :=
    (hasDerivAt_thetaCuspReflectedLogAction u t).const_mul 2
  have h := h1.sub h2
  refine h.congr_deriv ?_
  ring

/-- `t` times the derivative of the first shape deviation is exactly the difference of the two
shape deviations: the second deviation is determined by the profile of the first. -/
theorem mul_deriv_thetaCuspReflectedActionShapeDeviationOne (u t : ℝ) :
    t * (t * thetaCuspReflectedLogJetTwo u t - thetaCuspReflectedLogJetOne u t) =
      thetaCuspReflectedActionShapeDeviationTwo u t -
        thetaCuspReflectedActionShapeDeviationOne u t := by
  unfold thetaCuspReflectedActionShapeDeviationOne
    thetaCuspReflectedActionShapeDeviationTwo
  ring

/-- Both shape deviations vanish at zero displacement. -/
theorem thetaCuspReflectedActionShapeDeviation_zero (u : ℝ) :
    thetaCuspReflectedActionShapeDeviationOne u 0 = 0 ∧
      thetaCuspReflectedActionShapeDeviationTwo u 0 = 0 := by
  have haction : thetaCuspReflectedLogAction u 0 = 0 := by
    unfold thetaCuspReflectedLogAction
    rw [add_zero, sub_zero]
    ring
  constructor
  · unfold thetaCuspReflectedActionShapeDeviationOne
    rw [haction]
    ring
  · unfold thetaCuspReflectedActionShapeDeviationTwo
    rw [haction]
    ring

end

end RHTower
