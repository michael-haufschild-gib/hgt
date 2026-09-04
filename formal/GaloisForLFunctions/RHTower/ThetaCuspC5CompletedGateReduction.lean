import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodLiftReduction
import GaloisForLFunctions.HTGeometry.TanhSelfBound

/-!
# The completed C5 compensation gate in excess form

The direct-J gate of CLG/TTF is `0 < c5CompletedCompensationMargin u t`, i.e. `M(1) > 0` for the
likelihood homotopy.  Writing `H` for the completed fixed-action centre numerator,
`P` for the velocity--slope current numerator and `W = 14 + 10v + 8v/(e^Φ − 1)` for the Bose
weight (`v = tΦ_t` the action velocity, `Φ` the completed reflected action), the corpus proves
`M(1) = 5P − W·H` on `0 < t < u`.  This file records two purely algebraic facts and one
elementary inequality that reorganise the gate into a large-margin criterion.

* **Jet identity.**  `P = H + t·Ḣ`, where `Ḣ := tΦ_tΦ_utt − 2Φ_ttΦ_u − tΦ_tttΦ_u` is the literal
  displacement derivative of `H` written in the jets.  Hence
  `M(1) = (W − 30)·(−H) + 5·G`, `G := tḢ − 5H`  (the *scaling excess*: `H ≈ h₅t⁵` forces `G = O(t⁷)`).
* **Bose floor.**  If `v ≥ 2Φ > 0` then `W − 30 ≥ 12Φ`.  The only analytic input is
  `e^Φ ≤ (2 + Φ)/(2 − Φ)` on `[0, 2)`, i.e. `x ≤ artanh x`.
* **Assembly.**  `H < 0`, `v ≥ 2Φ` and `5|G| ≤ 6Φ·(−H)` give `M(1) ≥ 6Φ·(−H) > 0`.

Numerically (`clg_bounds.py`) the true ratios are `(W − 30)/Φ ≥ 12.02` and
`5|G|/(Φ·(−H)) ≤ 1.0` on the whole structural tail, so the assembly hypotheses carry a
sixfold margin.  The remaining analytic burden of the gate is therefore exactly the three
hypotheses `H < 0`, `v ≥ 2Φ`, `5|G| ≤ 6Φ(−H)`.
-/

namespace RHTower

noncomputable section

/-- Literal displacement derivative of the completed centre numerator, as a jet polynomial:
`Ḣ = tΦ_tΦ_utt − 2Φ_ttΦ_u − tΦ_tttΦ_u`. -/
def thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet (u t : ℝ) : ℝ :=
  let a := thetaCuspReflectedLogJetOne u t
  let b := thetaCuspReflectedLogJetTwo u t
  let c := thetaCuspReflectedLogJetThree u t
  let s := thetaCuspReflectedLogCenterJetOne u t
  let n := thetaCuspReflectedLogCenterMixedJetThree u t
  t * a * n - 2 * b * s - t * c * s

/-- The scaling excess `G = tḢ − 5H`. -/
def c5CompletedScalingExcess (u t : ℝ) : ℝ :=
  t * thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet u t -
    5 * thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t

/-- The completed Bose weight `W = 14 + 10v + 8v/(e^Φ − 1)`. -/
def c5CompletedBoseWeight (u t : ℝ) : ℝ :=
  14 + 10 * thetaCuspReflectedActionVelocity u t +
    8 * thetaCuspReflectedActionVelocity u t /
      (Real.exp (thetaCuspReflectedLogAction u t) - 1)

/-- **Jet identity.**  The velocity--slope current numerator is `H + tḢ`. -/
theorem slopeCurrentNumerator_eq_centerNumerator_add_timeJet (u t : ℝ) :
    thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator u t =
      thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t +
        t * thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet u t := by
  unfold thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator
    thetaCuspReflectedActionVelocityFixedActionCenterNumerator
    thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet
  ring

/-- **Excess form of the gate.**  `M(1) = (W − 30)(−H) + 5G` on the open chamber `0 < t < u`. -/
theorem c5CompletedCompensationMargin_eq_excess_form {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    c5CompletedCompensationMargin u t =
      (c5CompletedBoseWeight u t - 30) *
          (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t) +
        5 * c5CompletedScalingExcess u t := by
  rw [c5CompletedCompensationMargin_eq_intrinsic ht htu,
    slopeCurrentNumerator_eq_centerNumerator_add_timeJet]
  unfold c5CompletedBoseWeight c5CompletedScalingExcess
  ring

/-- `(x − 2)e^x + x + 2 ≥ 0` for `x ≥ 0`: the `(1,1)` Padé bound `e^x ≤ (2 + x)/(2 − x)` on
`[0, 2)`, obtained from `y ≤ artanh y`, and trivial beyond `2`. -/
theorem exp_padé_floor {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x - 2) * Real.exp x + x + 2 := by
  rcases lt_or_ge x 2 with h2 | h2
  · have hy0 : 0 ≤ x / 2 := by linarith
    have hy1 : x / 2 < 1 := by linarith
    have hart := GaloisForLFunctions.HTGeometry.self_le_artanh hy0 hy1
    rw [Real.artanh_eq_half_log ⟨by linarith, hy1⟩] at hart
    have hpos : 0 < (1 + x / 2) / (1 - x / 2) := by
      apply div_pos <;> linarith
    have hlog : x ≤ Real.log ((1 + x / 2) / (1 - x / 2)) := by linarith
    have hexp : Real.exp x ≤ (1 + x / 2) / (1 - x / 2) := by
      calc Real.exp x ≤ Real.exp (Real.log ((1 + x / 2) / (1 - x / 2))) :=
            Real.exp_le_exp.2 hlog
        _ = (1 + x / 2) / (1 - x / 2) := Real.exp_log hpos
    have hden : 0 < 1 - x / 2 := by linarith
    rw [le_div_iff₀ hden] at hexp
    nlinarith
  · have := Real.exp_pos x
    nlinarith

/-- **Bose floor.**  `v ≥ 2Φ` and `Φ > 0` give `W − 30 ≥ 12Φ`. -/
theorem twelve_mul_action_le_boseWeight_sub_thirty {u t : ℝ}
    (hΦ : 0 < thetaCuspReflectedLogAction u t)
    (hv : 2 * thetaCuspReflectedLogAction u t ≤ thetaCuspReflectedActionVelocity u t) :
    12 * thetaCuspReflectedLogAction u t ≤ c5CompletedBoseWeight u t - 30 := by
  set Φ := thetaCuspReflectedLogAction u t with hΦdef
  set v := thetaCuspReflectedActionVelocity u t with hvdef
  have hr : 0 < Real.exp Φ - 1 := by
    have : Real.exp 0 < Real.exp Φ := Real.exp_lt_exp.2 hΦ
    rw [Real.exp_zero] at this
    linarith
  unfold c5CompletedBoseWeight
  rw [← hΦdef, ← hvdef]
  -- `8v/r ≥ 16Φ/r` and `Φ(e^Φ − 1) + 2Φ ≥ 2(e^Φ − 1)`
  have hpade := exp_padé_floor hΦ.le
  have hkey : 16 * Φ / (Real.exp Φ - 1) ≥ 16 - 8 * Φ := by
    rw [ge_iff_le, le_div_iff₀ hr]
    nlinarith
  have h8 : 16 * Φ / (Real.exp Φ - 1) ≤ 8 * v / (Real.exp Φ - 1) := by
    apply div_le_div_of_nonneg_right _ hr.le
    linarith
  linarith

/-- **Assembly.**  `H < 0`, `v ≥ 2Φ` and `5|G| ≤ 6Φ(−H)` give `M(1) ≥ 6Φ(−H)`. -/
theorem six_mul_action_mul_neg_center_le_completedCompensationMargin {u t : ℝ}
    (ht : 0 < t) (htu : t < u)
    (hH : thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t < 0)
    (hv : 2 * thetaCuspReflectedLogAction u t ≤ thetaCuspReflectedActionVelocity u t)
    (hG : 5 * |c5CompletedScalingExcess u t| ≤
      6 * thetaCuspReflectedLogAction u t *
        (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t)) :
    6 * thetaCuspReflectedLogAction u t *
        (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t) ≤
      c5CompletedCompensationMargin u t := by
  have hΦ : 0 < thetaCuspReflectedLogAction u t := thetaCuspReflectedLogAction_pos ht
  have hW := twelve_mul_action_le_boseWeight_sub_thirty hΦ hv
  rw [c5CompletedCompensationMargin_eq_excess_form ht htu]
  set Φ := thetaCuspReflectedLogAction u t
  set H := thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t
  set G := c5CompletedScalingExcess u t
  set W := c5CompletedBoseWeight u t
  have hnegH : 0 < -H := by linarith
  have hGlow : -(6 * Φ * (-H)) ≤ 5 * G := by
    have := (abs_le.1 (show |5 * G| ≤ 6 * Φ * (-H) by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5)]; exact hG)).1
    linarith
  have hWH : 12 * Φ * (-H) ≤ (W - 30) * (-H) := mul_le_mul_of_nonneg_right hW hnegH.le
  nlinarith

/-- **The gate under the three analytic hypotheses.**  Direct-J orientation follows. -/
theorem c5CompletedCompensationMargin_pos_of_bounds {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hH : thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t < 0)
    (hv : 2 * thetaCuspReflectedLogAction u t ≤ thetaCuspReflectedActionVelocity u t)
    (hG : 5 * |c5CompletedScalingExcess u t| ≤
      6 * thetaCuspReflectedLogAction u t *
        (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t)) :
    0 < c5CompletedCompensationMargin u t := by
  have hΦ : 0 < thetaCuspReflectedLogAction u t := thetaCuspReflectedLogAction_pos ht
  have h := six_mul_action_mul_neg_center_le_completedCompensationMargin ht htu hH hv hG
  have : 0 < 6 * thetaCuspReflectedLogAction u t *
      (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t) := by
    apply mul_pos (by linarith) (by linarith)
  linarith

theorem thetaCuspReflectedActionC5FixedActionJacobian_pos_of_bounds {u t : ℝ} (ht : 0 < t)
    (htu : t < u)
    (hH : thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t < 0)
    (hv : 2 * thetaCuspReflectedLogAction u t ≤ thetaCuspReflectedActionVelocity u t)
    (hG : 5 * |c5CompletedScalingExcess u t| ≤
      6 * thetaCuspReflectedLogAction u t *
        (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t)) :
    0 < thetaCuspReflectedActionC5FixedActionJacobian u t :=
  (thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_completedCompensation ht htu).2
    (c5CompletedCompensationMargin_pos_of_bounds ht htu hH hv hG)

end

end RHTower
