import GaloisForLFunctions.RHTower.ThetaCuspC5CompletedGateReduction
import GaloisForLFunctions.RHTower.ThetaCuspC5CompletedGateSigns
import GaloisForLFunctions.RHTower.ThetaCuspC5RegimeOneCurvatureSigns

/-!
# The completed C5 compensation gate in regime I

For `0 < t ≤ u` with `A(u − t) = π e^{2(u−t)} ≥ 6` the two structural inputs of the gate
`M(1) > 0` are theorems:

* `H < 0` (centre negativity, `centerNumerator_neg_of_curvatureSigns` fed by the regime-I
  sign facts `(R2)`, `(R3)`, `(R4)` of `ThetaCuspC5RegimeOneCurvatureSigns`);
* `2Φ ≤ v` (Bose floor, `two_mul_action_le_velocity_of_jetTwo_nonneg` fed by `(R3)`).

The gate itself then reduces to the single growth bound `5|G| ≤ 6Φ(−H)` on the scaling
excess `G = tḢ − 5H`, which is exactly the log-derivative inequality
`t ∂ₜ log(−H) ≤ 5 + 2.4 Φ`.  That bound is the remaining open input and is stated as a
hypothesis here; everything else is unconditional.
-/

open Set

namespace RHTower

/-- Regime-I centre negativity: `H < 0` whenever `A(u − t) ≥ 6`. -/
theorem centerNumerator_neg_of_regimeOne {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t < 0 := by
  have hx₀ : 0 < u - t := regimeOne_pos_of_six_le hA
  have hmono : ∀ x : ℝ, u - t ≤ x → 6 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    intro x hx
    refine le_trans hA ?_
    unfold thetaCuspSingleAtomReflectionScale
    have := Real.exp_le_exp.mpr (show 2 * (u - t) ≤ 2 * x by linarith)
    simp only [Nat.cast_one, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_left this Real.pi_pos.le
  refine centerNumerator_neg_of_curvatureSigns ht htu hx₀.le le_rfl ?_ ?_ ?_
  · intro x hx _
    exact (regimeOne_curvature_signs (hmono x hx)).1
  · intro x hx
    exact (regimeOne_curvature_signs (hmono x hx)).2.1
  · intro x hx _
    exact (regimeOne_curvature_signs (hmono x hx)).2.2

/-- Regime-I Bose floor: `2Φ ≤ v` whenever `A(u − t) ≥ 6`. -/
theorem two_mul_action_le_velocity_of_regimeOne {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    2 * thetaCuspReflectedLogAction u t ≤ thetaCuspReflectedActionVelocity u t := by
  have hmono : ∀ x : ℝ, u - t ≤ x → 6 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    intro x hx
    refine le_trans hA ?_
    unfold thetaCuspSingleAtomReflectionScale
    have := Real.exp_le_exp.mpr (show 2 * (u - t) ≤ 2 * x by linarith)
    simp only [Nat.cast_one, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_left this Real.pi_pos.le
  refine two_mul_action_le_velocity_of_jetTwo_nonneg ht htu ?_
  intro x hx
  exact ((regimeOne_curvature_signs (hmono x hx)).2.1).le

/-- **Regime-I gate, conditional on the growth bound.**  With `A(u − t) ≥ 6`, the completed
compensation margin `M(1)` is positive as soon as `5|G| ≤ 6Φ(−H)`. -/
theorem c5CompletedCompensationMargin_pos_of_regimeOne {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t))
    (hG : 5 * |c5CompletedScalingExcess u t| ≤
      6 * thetaCuspReflectedLogAction u t *
        (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t)) :
    0 < c5CompletedCompensationMargin u t :=
  c5CompletedCompensationMargin_pos_of_bounds ht htu
    (centerNumerator_neg_of_regimeOne ht htu.le hA)
    (two_mul_action_le_velocity_of_regimeOne ht htu.le hA) hG

/-- The direct-Jacobian form of the regime-I gate. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_pos_of_regimeOne {u t : ℝ} (ht : 0 < t)
    (htu : t < u) (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t))
    (hG : 5 * |c5CompletedScalingExcess u t| ≤
      6 * thetaCuspReflectedLogAction u t *
        (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t)) :
    0 < thetaCuspReflectedActionC5FixedActionJacobian u t :=
  thetaCuspReflectedActionC5FixedActionJacobian_pos_of_bounds ht htu
    (centerNumerator_neg_of_regimeOne ht htu.le hA)
    (two_mul_action_le_velocity_of_regimeOne ht htu.le hA) hG

end RHTower
