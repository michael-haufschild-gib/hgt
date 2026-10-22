import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddCompactSourceCoordinates

/-!
# Explicit compact reserve for the literal correction

The literal source has a positive correction reserve on [0, 137/2000].
The correction dominates the squared theta mass throughout that interval.
-/

open Set
namespace RHTower
noncomputable section
set_option maxHeartbeats 2000000

/-- The compact comparison source has a fixed positive normalized reserve. -/
private theorem compactLowerSource_one_le {u a w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ha0 : 17 ≤ a) (ha1 : a ≤ 20)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    1 ≤ HTGeometry.oddCompactLowerSource u a w := by
  have hQ : (11/16 : ℝ) ≤ HTGeometry.oddCompactSourceZero u a := by
    unfold HTGeometry.oddCompactSourceZero
    nlinarith [sq_nonneg u]
  have haw : a*w ≤ 20 := by
    have h := mul_le_mul_of_nonneg_right ha1 hw0
    nlinarith
  have hloss : a*w/8+5*u/16 ≤ (45/16 : ℝ) := by linarith
  have hf : (3/2 : ℝ) ≤ 3*HTGeometry.oddCompactSourceZero u a -
      (137/1000 : ℝ)*(a*w/8+5*u/16) := by linarith
  have hmul := mul_le_mul hQ hf (by norm_num : (0 : ℝ) ≤ 3/2)
    (by linarith : 0 ≤ HTGeometry.oddCompactSourceZero u a)
  unfold HTGeometry.oddCompactLowerSource
  nlinarith only [hmul]

/-- Actual complete-source correction dominates the compact polynomial comparison source. -/
theorem thetaCuspCenterCompensationSource_compact_lower {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (137/2000)) :
    Bottcher.completedThetaProfile x^(2 : ℕ) *
      HTGeometry.oddCompactLowerSource (-(thetaCuspModularDrift x).re)
        (thetaCuspModularGapAmplitude x) (thetaCuspModularTransverseShear x) ≤
      thetaCuspCenterCompensationSource x := by
  obtain ⟨hS0, hS1, hA0, hA1, hW0, _⟩ := thetaCuspModularLyapunovState_compact_box hx
  let u := -(thetaCuspModularDrift x).re
  let a := thetaCuspModularGapAmplitude x
  let w := thetaCuspModularTransverseShear x
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hw : 0 ≤ w := hW0
  have hQ : 0 ≤ HTGeometry.oddCompactSourceZero u a := by
    unfold HTGeometry.oddCompactSourceZero
    change 17 ≤ a at hA0
    nlinarith [sq_nonneg u]
  have hloss : 0 ≤ a*w/8+5*u/16 := by positivity
  have hfirst : -(a*w/8+5*u/16) ≤ HTGeometry.oddCompactSourceFirst u a w := by
    have hp : 0 ≤ 5*u^(3 : ℕ)/144+7*u*a/96 := by positivity
    unfold HTGeometry.oddCompactSourceFirst
    linarith
  have hmul := mul_le_mul_of_nonneg_left hfirst
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx.1) hQ)
  have hxmul := mul_le_mul_of_nonneg_right hx.2 (mul_nonneg hQ hloss)
  have hbound : HTGeometry.oddCompactLowerSource u a w ≤
      3*(HTGeometry.oddCompactSourceZero u a)^(2 : ℕ) +
        2*x*HTGeometry.oddCompactSourceZero u a*HTGeometry.oddCompactSourceFirst u a w := by
    unfold HTGeometry.oddCompactLowerSource
    nlinarith only [hmul, hxmul]
  have hscaled := mul_le_mul_of_nonneg_left hbound
    (sq_nonneg (Bottcher.completedThetaProfile x))
  unfold thetaCuspCenterCompensationSource
  rw [thetaCuspFullSource_eq_compactSourceZero, deriv_thetaCuspFullSource_eq_compactSourceFirst]
  change Bottcher.completedThetaProfile x^(2 : ℕ) * HTGeometry.oddCompactLowerSource u a w ≤ _
  nlinarith only [hscaled]

/-- A fixed positive source reserve on the explicit compact center interval. -/
theorem thetaCuspCenterCompensationSource_ge_mass_sq_on_compact {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (137/2000)) :
    Bottcher.completedThetaProfile x^(2 : ℕ) ≤ thetaCuspCenterCompensationSource x := by
  obtain ⟨hS0, hS1, hA0, hA1, hW0, _⟩ := thetaCuspModularLyapunovState_compact_box hx
  have hu0 : 0 ≤ -(thetaCuspModularDrift x).re := by linarith
  have hu1 : -(thetaCuspModularDrift x).re ≤ 1 := by linarith
  have hb := compactLowerSource_one_le hu0 hu1 hA0 hA1 hW0
    (thetaCuspModularTransverseShear_le_one_on_compact hx)
  have h := mul_le_mul_of_nonneg_left hb (sq_nonneg (Bottcher.completedThetaProfile x))
  have hh : Bottcher.completedThetaProfile x^(2 : ℕ) ≤
      Bottcher.completedThetaProfile x^(2 : ℕ) *
        HTGeometry.oddCompactLowerSource (-(thetaCuspModularDrift x).re)
          (thetaCuspModularGapAmplitude x) (thetaCuspModularTransverseShear x) := by
    simpa only [mul_one] using h
  exact hh.trans (thetaCuspCenterCompensationSource_compact_lower hx)

end
end RHTower
