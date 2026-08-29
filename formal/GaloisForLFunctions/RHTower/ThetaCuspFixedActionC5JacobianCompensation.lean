import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5JacobianGermClosure

/-!
# Exact compensation law for direct fixed-action C5 transport

The corpus's naïve two-sign velocity transport is false at the theta seam.  This module retains
the compensating terms and proves that direct-J orientation is exactly one sharp inequality
between division-free velocity transport and velocity--slope current transport.
-/

namespace RHTower

noncomputable section

/-- Division-free fixed-action centre transport numerator of intrinsic action velocity. -/
def thetaCuspReflectedActionVelocityFixedActionCenterNumerator (u t : ℝ) : ℝ :=
  let a := thetaCuspReflectedLogJetOne u t
  let b := thetaCuspReflectedLogJetTwo u t
  let s := thetaCuspReflectedLogCenterJetOne u t
  let m := thetaCuspReflectedLogCenterMixedJetOne u t
  a * (t * m) - (a + t * b) * s

/-- Division-free fixed-action centre transport numerator of the velocity--slope product. -/
def thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator
    (u t : ℝ) : ℝ :=
  let a := thetaCuspReflectedLogJetOne u t
  let b := thetaCuspReflectedLogJetTwo u t
  let c := thetaCuspReflectedLogJetThree u t
  let s := thetaCuspReflectedLogCenterJetOne u t
  let m := thetaCuspReflectedLogCenterMixedJetOne u t
  let n := thetaCuspReflectedLogCenterMixedJetThree u t
  a * (t * m + t ^ 2 * n) - (a + 3 * t * b + t ^ 2 * c) * s

/-- Exact compensation law for direct fixed-action C5 transport.  The direct Jacobian is the
velocity--slope current transport minus a strictly weighted velocity transport, after clearing
only the positive action radius. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_compensation
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    4 * (Real.exp (thetaCuspReflectedLogAction u t) - 1) *
        thetaCuspReflectedActionC5FixedActionJacobian u t =
      5 * thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator u t -
        (14 + 10 * thetaCuspReflectedActionVelocity u t +
          8 * thetaCuspReflectedActionVelocity u t /
            (Real.exp (thetaCuspReflectedLogAction u t) - 1)) *
          thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t := by
  have hr : Real.exp (thetaCuspReflectedLogAction u t) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht))
  unfold thetaCuspReflectedActionC5FixedActionJacobian
    thetaCuspReflectedActionC5CenterDerivative
    thetaCuspReflectedActionC5DisplacementDerivative
    thetaCuspReflectedActionC5PartialAction
    thetaCuspReflectedActionC5PartialJetOne
    thetaCuspReflectedActionC5PartialJetTwo
    thetaCuspReflectedActionC5PartialDisplacement
    thetaCuspReflectedActionInverseRadius
    thetaCuspReflectedActionVelocity
    thetaCuspReflectedActionVelocityFixedActionCenterNumerator
    thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator
  dsimp only
  field_simp [hr]
  ring

/-- Direct-J nonnegativity is exactly one compensated source-transport inequality. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_nonneg_iff_compensation
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ thetaCuspReflectedActionC5FixedActionJacobian u t ↔
      (14 + 10 * thetaCuspReflectedActionVelocity u t +
          8 * thetaCuspReflectedActionVelocity u t /
            (Real.exp (thetaCuspReflectedLogAction u t) - 1)) *
          thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t ≤
        5 * thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator u t := by
  have hr : 0 < Real.exp (thetaCuspReflectedLogAction u t) - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht)
  rw [← mul_nonneg_iff_of_pos_left (mul_pos (by norm_num : (0 : ℝ) < 4) hr)]
  rw [thetaCuspReflectedActionC5FixedActionJacobian_compensation u ht]
  exact sub_nonneg

/-- Strict direct-J orientation is exactly strict compensated source transport. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_compensation
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedActionC5FixedActionJacobian u t ↔
      (14 + 10 * thetaCuspReflectedActionVelocity u t +
          8 * thetaCuspReflectedActionVelocity u t /
            (Real.exp (thetaCuspReflectedLogAction u t) - 1)) *
          thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t <
        5 * thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator u t := by
  have hr : 0 < Real.exp (thetaCuspReflectedLogAction u t) - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht)
  rw [← mul_pos_iff_of_pos_left (mul_pos (by norm_num : (0 : ℝ) < 4) hr)]
  rw [thetaCuspReflectedActionC5FixedActionJacobian_compensation u ht]
  exact sub_pos

end

end RHTower
