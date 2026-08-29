import GaloisForLFunctions.RHTower.ThetaCuspReflectedActionVelocityBalance

open Set

namespace RHTower

noncomputable section

/-!
# Direct fixed-action C5 Jacobian

The normalized completed-theta C5 balance is differentiated in centre and displacement
coordinates without numerical input. Contracting those derivatives with the reflected-action
gradient gives the exact tangent derivative along fixed-action level sets. The remaining research
burden is positivity of one explicit source-jet Jacobian on `u > 0`, `t > 0`.
-/

/-- Reciprocal exponential radius of the reflected logarithmic action. -/
def thetaCuspReflectedActionInverseRadius (u t : ℝ) : ℝ :=
  1 / (Real.exp (thetaCuspReflectedLogAction u t) - 1)

/-- Normalized C5 balance written directly in the first two displacement jets. -/
def thetaCuspReflectedActionC5DirectBalance (u t : ℝ) : ℝ :=
  let R := thetaCuspReflectedActionInverseRadius u t
  let a := thetaCuspReflectedLogJetOne u t
  let b := thetaCuspReflectedLogJetTwo u t
  6 - (9 / 4 : ℝ) * t * a * R +
    (5 / 4 : ℝ) * t ^ 2 * (b - a ^ 2) * R - t ^ 2 * a ^ 2 * R ^ 2

/-- Formal partial derivative of direct C5 balance with respect to action. -/
def thetaCuspReflectedActionC5PartialAction (u t : ℝ) : ℝ :=
  let R := thetaCuspReflectedActionInverseRadius u t
  let a := thetaCuspReflectedLogJetOne u t
  let b := thetaCuspReflectedLogJetTwo u t
  (-(9 / 4 : ℝ) * t * a + (5 / 4 : ℝ) * t ^ 2 * (b - a ^ 2) -
      2 * t ^ 2 * a ^ 2 * R) * (-R - R ^ 2)

/-- Formal partial derivative of direct C5 balance with respect to first displacement jet. -/
def thetaCuspReflectedActionC5PartialJetOne (u t : ℝ) : ℝ :=
  let R := thetaCuspReflectedActionInverseRadius u t
  let a := thetaCuspReflectedLogJetOne u t
  (-(9 / 4 : ℝ) * t * R - (5 / 2 : ℝ) * t ^ 2 * a * R -
    2 * t ^ 2 * a * R ^ 2)

/-- Formal partial derivative of direct C5 balance with respect to second displacement jet. -/
def thetaCuspReflectedActionC5PartialJetTwo (u t : ℝ) : ℝ :=
  (5 / 4 : ℝ) * t ^ 2 * thetaCuspReflectedActionInverseRadius u t

/-- Explicit-displacement partial derivative of direct C5 balance. -/
def thetaCuspReflectedActionC5PartialDisplacement (u t : ℝ) : ℝ :=
  let R := thetaCuspReflectedActionInverseRadius u t
  let a := thetaCuspReflectedLogJetOne u t
  let b := thetaCuspReflectedLogJetTwo u t
  (-(9 / 4 : ℝ) * a * R + (5 / 2 : ℝ) * t * (b - a ^ 2) * R -
    2 * t * a ^ 2 * R ^ 2)

/-- Centre derivative of the second reflected displacement jet. -/
def thetaCuspReflectedLogCenterMixedJetThree (u t : ℝ) : ℝ :=
  thetaCuspLogCurvatureJet (u + t) + thetaCuspLogCurvatureJet (u - t)

/-- Exact source-jet expression for the centre derivative of direct C5 balance. -/
def thetaCuspReflectedActionC5CenterDerivative (u t : ℝ) : ℝ :=
  thetaCuspReflectedActionC5PartialAction u t *
      thetaCuspReflectedLogCenterJetOne u t +
    thetaCuspReflectedActionC5PartialJetOne u t *
      thetaCuspReflectedLogCenterMixedJetOne u t +
    thetaCuspReflectedActionC5PartialJetTwo u t *
      thetaCuspReflectedLogCenterMixedJetThree u t

/-- Exact source-jet expression for the displacement derivative of direct C5 balance. -/
def thetaCuspReflectedActionC5DisplacementDerivative (u t : ℝ) : ℝ :=
  thetaCuspReflectedActionC5PartialDisplacement u t +
    thetaCuspReflectedActionC5PartialAction u t * thetaCuspReflectedLogJetOne u t +
    thetaCuspReflectedActionC5PartialJetOne u t * thetaCuspReflectedLogJetTwo u t +
    thetaCuspReflectedActionC5PartialJetTwo u t * thetaCuspReflectedLogJetThree u t

/-- Oriented tangent derivative of C5 balance along fixed-action level sets. -/
def thetaCuspReflectedActionC5FixedActionJacobian (u t : ℝ) : ℝ :=
  thetaCuspReflectedActionC5CenterDerivative u t * thetaCuspReflectedLogJetOne u t -
    thetaCuspReflectedActionC5DisplacementDerivative u t *
      thetaCuspReflectedLogCenterJetOne u t

/-- Direct two-jet balance equals the intrinsic action-velocity balance. -/
theorem thetaCuspReflectedActionC5DirectBalance_eq_velocityBalance
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedActionC5DirectBalance u t =
      thetaCuspReflectedActionVelocityC5Balance u t := by
  have ha := (thetaCuspReflectedLogJetOne_pos u ht).ne'
  have hr : Real.exp (thetaCuspReflectedLogAction u t) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht))
  unfold thetaCuspReflectedActionC5DirectBalance
    thetaCuspReflectedActionInverseRadius
    thetaCuspReflectedActionVelocityC5Balance
    thetaCuspReflectedActionVelocity thetaCuspReflectedActionVelocitySlope
  dsimp only
  field_simp [ha, hr]
  ring

/-- Centre derivative of reciprocal action radius. -/
theorem hasDerivAt_thetaCuspReflectedActionInverseRadius_center
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => thetaCuspReflectedActionInverseRadius x t)
      ((-thetaCuspReflectedActionInverseRadius u t -
          thetaCuspReflectedActionInverseRadius u t ^ 2) *
        thetaCuspReflectedLogCenterJetOne u t) u := by
  have hq := hasDerivAt_thetaCuspReflectedLogAction_center u t
  have hr := hq.exp.sub_const 1
  have hrne : Real.exp (thetaCuspReflectedLogAction u t) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht))
  have hraw := (hasDerivAt_const u 1).div hr hrne
  refine hraw.congr_deriv ?_
  unfold thetaCuspReflectedActionInverseRadius
  field_simp [hrne]
  ring

/-- Displacement derivative of reciprocal action radius. -/
theorem hasDerivAt_thetaCuspReflectedActionInverseRadius_displacement
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspReflectedActionInverseRadius u)
      ((-thetaCuspReflectedActionInverseRadius u t -
          thetaCuspReflectedActionInverseRadius u t ^ 2) *
        thetaCuspReflectedLogJetOne u t) t := by
  have hq := hasDerivAt_thetaCuspReflectedLogAction u t
  have hr := hq.exp.sub_const 1
  have hrne : Real.exp (thetaCuspReflectedLogAction u t) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht))
  have hraw := (hasDerivAt_const t 1).div hr hrne
  refine hraw.congr_deriv ?_
  unfold thetaCuspReflectedActionInverseRadius
  field_simp [hrne]
  ring

/-- Direct C5 balance differentiates in centre by its named exact source-jet expression. -/
theorem hasDerivAt_thetaCuspReflectedActionC5DirectBalance_center
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => thetaCuspReflectedActionC5DirectBalance x t)
      (thetaCuspReflectedActionC5CenterDerivative u t) u := by
  let R : ℝ → ℝ := fun x => thetaCuspReflectedActionInverseRadius x t
  let A : ℝ → ℝ := fun x => thetaCuspReflectedLogJetOne x t
  let B : ℝ → ℝ := fun x => thetaCuspReflectedLogJetTwo x t
  have hR : HasDerivAt R
      ((-R u - R u ^ 2) * thetaCuspReflectedLogCenterJetOne u t) u := by
    simpa only [R] using hasDerivAt_thetaCuspReflectedActionInverseRadius_center u ht
  have hA : HasDerivAt A (thetaCuspReflectedLogCenterMixedJetOne u t) u := by
    simpa only [A] using hasDerivAt_thetaCuspReflectedLogJetOne_center u t
  have hB : HasDerivAt B (thetaCuspReflectedLogCenterMixedJetThree u t) u := by
    simpa only [B, thetaCuspReflectedLogCenterMixedJetThree] using
      hasDerivAt_thetaCuspReflectedLogJetTwo_center u t
  have hraw := (((hasDerivAt_const u 6).sub
      (((hA.const_mul t).const_mul (9 / 4 : ℝ)).mul hR)).add
      (((hB.sub (hA.pow 2)).const_mul (t ^ 2)).const_mul (5 / 4 : ℝ) |>.mul hR)).sub
      (((hA.pow 2).const_mul (t ^ 2)).mul (hR.pow 2))
  refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · simp only [R, A, B, Pi.add_apply, Pi.sub_apply,
      Pi.pow_apply, Pi.mul_apply]
    unfold thetaCuspReflectedActionC5DirectBalance
    ring
  · simp only [R, A, B, Pi.sub_apply, Pi.pow_apply]
    unfold thetaCuspReflectedActionC5CenterDerivative
      thetaCuspReflectedActionC5PartialAction
      thetaCuspReflectedActionC5PartialJetOne
      thetaCuspReflectedActionC5PartialJetTwo
    ring

/-- Direct C5 balance differentiates in displacement by its named exact source-jet expression. -/
theorem hasDerivAt_thetaCuspReflectedActionC5DirectBalance_displacement
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspReflectedActionC5DirectBalance u)
      (thetaCuspReflectedActionC5DisplacementDerivative u t) t := by
  let R : ℝ → ℝ := thetaCuspReflectedActionInverseRadius u
  let A : ℝ → ℝ := thetaCuspReflectedLogJetOne u
  let B : ℝ → ℝ := thetaCuspReflectedLogJetTwo u
  have hR : HasDerivAt R
      ((-R t - R t ^ 2) * thetaCuspReflectedLogJetOne u t) t := by
    simpa only [R] using hasDerivAt_thetaCuspReflectedActionInverseRadius_displacement u ht
  have hA : HasDerivAt A (thetaCuspReflectedLogJetTwo u t) t := by
    simpa only [A] using hasDerivAt_thetaCuspReflectedLogJetOne u t
  have hB : HasDerivAt B (thetaCuspReflectedLogJetThree u t) t := by
    simpa only [B] using hasDerivAt_thetaCuspReflectedLogJetTwo u t
  have hT := hasDerivAt_id t
  have hraw := (((hasDerivAt_const t 6).sub
      ((((hT.mul hA).const_mul (9 / 4 : ℝ))).mul hR)).add
      (((((hT.pow 2).mul (hB.sub (hA.pow 2))).const_mul (5 / 4 : ℝ))).mul hR)).sub
      (((hT.pow 2).mul (hA.pow 2)).mul (hR.pow 2))
  refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · simp only [R, A, B, Pi.add_apply, Pi.sub_apply,
      Pi.pow_apply, Pi.mul_apply, id_eq]
    unfold thetaCuspReflectedActionC5DirectBalance
    ring
  · simp only [R, A, B, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq]
    unfold thetaCuspReflectedActionC5DisplacementDerivative
      thetaCuspReflectedActionC5PartialDisplacement
      thetaCuspReflectedActionC5PartialAction
      thetaCuspReflectedActionC5PartialJetOne
      thetaCuspReflectedActionC5PartialJetTwo
    ring

/-- Named Jacobian is exactly the determinant of C5 and action gradients. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_eq_deriv
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedActionC5FixedActionJacobian u t =
      deriv (fun x => thetaCuspReflectedActionC5DirectBalance x t) u *
          deriv (thetaCuspReflectedLogAction u) t -
        deriv (thetaCuspReflectedActionC5DirectBalance u) t *
          deriv (fun x => thetaCuspReflectedLogAction x t) u := by
  rw [(hasDerivAt_thetaCuspReflectedActionC5DirectBalance_center u ht).deriv,
    (hasDerivAt_thetaCuspReflectedActionC5DirectBalance_displacement u ht).deriv,
    (hasDerivAt_thetaCuspReflectedLogAction u t).deriv,
    (hasDerivAt_thetaCuspReflectedLogAction_center u t).deriv]
  rfl

/-- Reflection forces the fixed-action C5 Jacobian to vanish at the modular seam. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_zero (t : ℝ) :
    thetaCuspReflectedActionC5FixedActionJacobian 0 t = 0 := by
  have hs0 : thetaCuspLogDecaySlope 0 = 0 := by
    have h := thetaCuspLogDecaySlope_neg 0
    norm_num at h
    linarith
  unfold thetaCuspReflectedActionC5FixedActionJacobian
    thetaCuspReflectedActionC5CenterDerivative
    thetaCuspReflectedActionC5DisplacementDerivative
    thetaCuspReflectedLogCenterJetOne
    thetaCuspReflectedLogCenterMixedJetOne
    thetaCuspReflectedLogCenterMixedJetThree
  simp only [zero_add, zero_sub, thetaCuspLogDecaySlope_neg,
    thetaCuspLogCurvature_neg, thetaCuspLogCurvatureJet_neg, hs0]
  ring

/-! ## Exact centre parity and desingularization -/

theorem thetaCuspReflectedLogAction_neg_center (u t : ℝ) :
    thetaCuspReflectedLogAction (-u) t = thetaCuspReflectedLogAction u t := by
  unfold thetaCuspReflectedLogAction
  rw [show -u + t = -(u - t) by ring,
    show -u - t = -(u + t) by ring,
    thetaCuspLogSource_neg, thetaCuspLogSource_neg, thetaCuspLogSource_neg]
  ring

theorem thetaCuspReflectedLogJetOne_neg_center (u t : ℝ) :
    thetaCuspReflectedLogJetOne (-u) t = thetaCuspReflectedLogJetOne u t := by
  unfold thetaCuspReflectedLogJetOne
  rw [show -u + t = -(u - t) by ring,
    show -u - t = -(u + t) by ring,
    thetaCuspLogDecaySlope_neg, thetaCuspLogDecaySlope_neg]
  ring

theorem thetaCuspReflectedLogJetTwo_neg_center (u t : ℝ) :
    thetaCuspReflectedLogJetTwo (-u) t = thetaCuspReflectedLogJetTwo u t := by
  unfold thetaCuspReflectedLogJetTwo
  rw [show -u + t = -(u - t) by ring,
    show -u - t = -(u + t) by ring,
    thetaCuspLogCurvature_neg, thetaCuspLogCurvature_neg]
  ring

theorem thetaCuspReflectedLogJetThree_neg_center (u t : ℝ) :
    thetaCuspReflectedLogJetThree (-u) t = thetaCuspReflectedLogJetThree u t := by
  unfold thetaCuspReflectedLogJetThree
  rw [show -u + t = -(u - t) by ring,
    show -u - t = -(u + t) by ring,
    thetaCuspLogCurvatureJet_neg, thetaCuspLogCurvatureJet_neg]
  ring

theorem thetaCuspReflectedLogCenterJetOne_neg_center (u t : ℝ) :
    thetaCuspReflectedLogCenterJetOne (-u) t =
      -thetaCuspReflectedLogCenterJetOne u t := by
  unfold thetaCuspReflectedLogCenterJetOne
  rw [show -u + t = -(u - t) by ring,
    show -u - t = -(u + t) by ring,
    thetaCuspLogDecaySlope_neg, thetaCuspLogDecaySlope_neg,
    thetaCuspLogDecaySlope_neg]
  ring

theorem thetaCuspReflectedLogCenterMixedJetOne_neg_center (u t : ℝ) :
    thetaCuspReflectedLogCenterMixedJetOne (-u) t =
      -thetaCuspReflectedLogCenterMixedJetOne u t := by
  unfold thetaCuspReflectedLogCenterMixedJetOne
  rw [show -u + t = -(u - t) by ring,
    show -u - t = -(u + t) by ring,
    thetaCuspLogCurvature_neg, thetaCuspLogCurvature_neg]
  ring

theorem thetaCuspReflectedLogCenterMixedJetThree_neg_center (u t : ℝ) :
    thetaCuspReflectedLogCenterMixedJetThree (-u) t =
      -thetaCuspReflectedLogCenterMixedJetThree u t := by
  unfold thetaCuspReflectedLogCenterMixedJetThree
  rw [show -u + t = -(u - t) by ring,
    show -u - t = -(u + t) by ring,
    thetaCuspLogCurvatureJet_neg, thetaCuspLogCurvatureJet_neg]
  ring

theorem thetaCuspReflectedActionInverseRadius_neg_center (u t : ℝ) :
    thetaCuspReflectedActionInverseRadius (-u) t =
      thetaCuspReflectedActionInverseRadius u t := by
  unfold thetaCuspReflectedActionInverseRadius
  rw [thetaCuspReflectedLogAction_neg_center]

theorem thetaCuspReflectedActionC5PartialAction_neg_center (u t : ℝ) :
    thetaCuspReflectedActionC5PartialAction (-u) t =
      thetaCuspReflectedActionC5PartialAction u t := by
  unfold thetaCuspReflectedActionC5PartialAction
  rw [thetaCuspReflectedActionInverseRadius_neg_center,
    thetaCuspReflectedLogJetOne_neg_center,
    thetaCuspReflectedLogJetTwo_neg_center]

theorem thetaCuspReflectedActionC5PartialJetOne_neg_center (u t : ℝ) :
    thetaCuspReflectedActionC5PartialJetOne (-u) t =
      thetaCuspReflectedActionC5PartialJetOne u t := by
  unfold thetaCuspReflectedActionC5PartialJetOne
  rw [thetaCuspReflectedActionInverseRadius_neg_center,
    thetaCuspReflectedLogJetOne_neg_center]

theorem thetaCuspReflectedActionC5PartialJetTwo_neg_center (u t : ℝ) :
    thetaCuspReflectedActionC5PartialJetTwo (-u) t =
      thetaCuspReflectedActionC5PartialJetTwo u t := by
  unfold thetaCuspReflectedActionC5PartialJetTwo
  rw [thetaCuspReflectedActionInverseRadius_neg_center]

theorem thetaCuspReflectedActionC5PartialDisplacement_neg_center (u t : ℝ) :
    thetaCuspReflectedActionC5PartialDisplacement (-u) t =
      thetaCuspReflectedActionC5PartialDisplacement u t := by
  unfold thetaCuspReflectedActionC5PartialDisplacement
  rw [thetaCuspReflectedActionInverseRadius_neg_center,
    thetaCuspReflectedLogJetOne_neg_center,
    thetaCuspReflectedLogJetTwo_neg_center]

theorem thetaCuspReflectedActionC5CenterDerivative_neg_center (u t : ℝ) :
    thetaCuspReflectedActionC5CenterDerivative (-u) t =
      -thetaCuspReflectedActionC5CenterDerivative u t := by
  unfold thetaCuspReflectedActionC5CenterDerivative
  rw [thetaCuspReflectedActionC5PartialAction_neg_center,
    thetaCuspReflectedActionC5PartialJetOne_neg_center,
    thetaCuspReflectedActionC5PartialJetTwo_neg_center,
    thetaCuspReflectedLogCenterJetOne_neg_center,
    thetaCuspReflectedLogCenterMixedJetOne_neg_center,
    thetaCuspReflectedLogCenterMixedJetThree_neg_center]
  ring

theorem thetaCuspReflectedActionC5DisplacementDerivative_neg_center (u t : ℝ) :
    thetaCuspReflectedActionC5DisplacementDerivative (-u) t =
      thetaCuspReflectedActionC5DisplacementDerivative u t := by
  unfold thetaCuspReflectedActionC5DisplacementDerivative
  rw [thetaCuspReflectedActionC5PartialDisplacement_neg_center,
    thetaCuspReflectedActionC5PartialAction_neg_center,
    thetaCuspReflectedActionC5PartialJetOne_neg_center,
    thetaCuspReflectedActionC5PartialJetTwo_neg_center,
    thetaCuspReflectedLogJetOne_neg_center,
    thetaCuspReflectedLogJetTwo_neg_center,
    thetaCuspReflectedLogJetThree_neg_center]

/-- Reflection makes the direct fixed-action C5 Jacobian odd in centre. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_neg_center (u t : ℝ) :
    thetaCuspReflectedActionC5FixedActionJacobian (-u) t =
      -thetaCuspReflectedActionC5FixedActionJacobian u t := by
  unfold thetaCuspReflectedActionC5FixedActionJacobian
  rw [thetaCuspReflectedActionC5CenterDerivative_neg_center,
    thetaCuspReflectedActionC5DisplacementDerivative_neg_center,
    thetaCuspReflectedLogJetOne_neg_center,
    thetaCuspReflectedLogCenterJetOne_neg_center]
  ring

/-- Quotient by centre removes the reflection-forced odd factor. Lean's total division makes
the definition global; its value at the seam is zero and its analytic seam extension is a
separate research object. -/
def thetaCuspReflectedActionC5FixedActionJacobianQuotient (u t : ℝ) : ℝ :=
  thetaCuspReflectedActionC5FixedActionJacobian u t / u

/-- The algebraically desingularized fixed-action C5 Jacobian is even in centre. -/
theorem thetaCuspReflectedActionC5FixedActionJacobianQuotient_neg_center (u t : ℝ) :
    thetaCuspReflectedActionC5FixedActionJacobianQuotient (-u) t =
      thetaCuspReflectedActionC5FixedActionJacobianQuotient u t := by
  unfold thetaCuspReflectedActionC5FixedActionJacobianQuotient
  rw [thetaCuspReflectedActionC5FixedActionJacobian_neg_center]
  ring

end

end RHTower
