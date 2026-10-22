import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddCompensationCoefficient

/-!
# Exact sign transition of the center compensation source

Strict logarithmic concavity forces the normalized correction to decrease from
three through one positive zero. The literal correction has exactly this sign
pattern because its source square is positive everywhere.
-/

open Set
namespace RHTower
noncomputable section

/-- Normalized sign carrier of the aperture-independent center correction. -/
def thetaCuspCenterCompensationSign (x : ℝ) : ℝ :=
  3 + 2*x*deriv thetaCuspLogSource x

/-- Removing the positive source square preserves exactly the correction sign. -/
theorem thetaCuspCenterCompensationSource_eq_sign (x : ℝ) :
    thetaCuspCenterCompensationSource x =
      thetaCuspFullSource x^(2 : ℕ) * thetaCuspCenterCompensationSign x := by
  rw [thetaCuspCenterCompensationSign, (hasDerivAt_thetaCuspLogSource x).deriv]
  simp only [iteratedDeriv_one]
  unfold thetaCuspCenterCompensationSource
  field_simp [(thetaCuspFullSource_pos_all x).ne']

private theorem logSlope_strictAnti : StrictAnti (deriv thetaCuspLogSource) :=
  strictAntiOn_univ.mp <|
    strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun x _ =>
      (hasDerivAt_thetaCuspLogSource x).differentiableAt

private theorem logSlope_zero : deriv thetaCuspLogSource 0 = 0 := by
  simpa only [iteratedDeriv_one] using
    (iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) (by norm_num : Odd 1))

private theorem logSlope_neg {x : ℝ} (hx : 0 < x) :
    deriv thetaCuspLogSource x < 0 := by
  simpa only [logSlope_zero] using logSlope_strictAnti hx

/-- The normalized correction decreases strictly along the complete physical ray. -/
theorem strictAntiOn_thetaCuspCenterCompensationSign :
    StrictAntiOn thetaCuspCenterCompensationSign (Ici 0) := by
  intro a ha b hb hab
  have hb0 : 0 < b := lt_of_le_of_lt ha hab
  have hl := logSlope_neg hb0
  have h1 := mul_lt_mul_of_neg_right hab hl
  have h2 := mul_le_mul_of_nonneg_left (logSlope_strictAnti hab).le ha
  unfold thetaCuspCenterCompensationSign
  nlinarith only [h1, h2]

/-- The complete-source normalized correction is continuous. -/
theorem continuous_thetaCuspCenterCompensationSign :
    Continuous thetaCuspCenterCompensationSign := by
  have hd : Continuous (deriv thetaCuspLogSource) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    simpa only [iteratedDeriv_one] using
      (hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x).continuousAt
  unfold thetaCuspCenterCompensationSign
  fun_prop

/-- Exactly one positive center separates helpful and adverse constant compensation. -/
theorem exists_thetaCuspCenterCompensationSign_transition :
    ∃ τ : ℝ, 0 < τ ∧ thetaCuspCenterCompensationSign τ = 0 ∧
      (∀ x : ℝ, 0 ≤ x →
        (0 < thetaCuspCenterCompensationSign x ↔ x < τ) ∧
        (thetaCuspCenterCompensationSign x = 0 ↔ x = τ) ∧
        (thetaCuspCenterCompensationSign x < 0 ↔ τ < x)) := by
  have hl := logSlope_neg (by norm_num : (0 : ℝ) < 1)
  let T : ℝ := 1 + (-4)/deriv thetaCuspLogSource 1
  have hT : 1 < T := by
    have hq : 0 < (-4)/deriv thetaCuspLogSource 1 :=
      div_pos_of_neg_of_neg (by norm_num) hl
    dsimp [T]
    linarith
  have hprod : (T-1)*deriv thetaCuspLogSource 1 = -4 := by
    dsimp [T]
    field_simp [hl.ne]
    ring
  have hneg : thetaCuspCenterCompensationSign T < 0 := by
    have hcomp := mul_le_mul_of_nonneg_left (logSlope_strictAnti hT).le
      (by linarith : 0 ≤ 2*T)
    unfold thetaCuspCenterCompensationSign
    nlinarith only [hcomp, hprod, hl]
  have hzero : thetaCuspCenterCompensationSign 0 = 3 := by
    simp [thetaCuspCenterCompensationSign]
  obtain ⟨τ, hτ, heq⟩ := intermediate_value_Icc' (by linarith : (0 : ℝ) ≤ T)
    continuous_thetaCuspCenterCompensationSign.continuousOn
    (show (0 : ℝ) ∈ Icc (thetaCuspCenterCompensationSign T)
      (thetaCuspCenterCompensationSign 0) from ⟨hneg.le, by rw [hzero]; norm_num⟩)
  have hτ0 : 0 < τ := by
    rcases hτ.1.eq_or_lt with h | h
    · subst τ
      linarith
    · exact h
  refine ⟨τ, hτ0, heq, fun x hx => ?_⟩
  have hi := strictAntiOn_thetaCuspCenterCompensationSign
  have hpos : 0 < thetaCuspCenterCompensationSign x ↔ x < τ := by
    rw [← heq]
    exact hi.lt_iff_gt hτ0.le hx
  have hneg' : thetaCuspCenterCompensationSign x < 0 ↔ τ < x := by
    rw [← heq]
    exact hi.lt_iff_gt hx hτ0.le
  refine ⟨hpos, ?_, hneg'⟩
  constructor
  · intro h
    rcases lt_trichotomy x τ with hlt | he | hgt
    · have := hpos.mpr hlt
      linarith
    · exact he
    · have := hneg'.mpr hgt
      linarith
  · intro h
    simpa only [h] using heq

/-- Literal correction, with its positive source mass restored, has the same unique transition. -/
theorem exists_thetaCuspCenterCompensationSource_transition :
    ∃ τ : ℝ, 0 < τ ∧
      (∀ x : ℝ, 0 ≤ x →
        (0 < thetaCuspCenterCompensationSource x ↔ x < τ) ∧
        (thetaCuspCenterCompensationSource x = 0 ↔ x = τ) ∧
        (thetaCuspCenterCompensationSource x < 0 ↔ τ < x)) := by
  obtain ⟨τ, hτ, _, hs⟩ := exists_thetaCuspCenterCompensationSign_transition
  refine ⟨τ, hτ, fun x hx => ?_⟩
  have hp : 0 < thetaCuspFullSource x^(2 : ℕ) := sq_pos_of_pos (thetaCuspFullSource_pos_all x)
  rw [thetaCuspCenterCompensationSource_eq_sign]
  simpa only [mul_pos_iff_of_pos_left hp, mul_eq_zero, hp.ne', false_or,
    mul_neg_iff, not_lt.mpr hp.le, false_and, or_false, hp, true_and] using hs x hx

end
end RHTower
