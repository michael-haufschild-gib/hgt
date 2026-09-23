import GaloisForLFunctions.RHTower.ThetaCuspOddEnergyCompensation
import GaloisForLFunctions.RHTower.ThetaCuspEvenCompactState

/-! # A stronger complete-source correction bound for the even compact comparison -/
namespace RHTower
noncomputable section
open Set

private abbrev u := thetaCuspModularMassDrift
private abbrev a := thetaCuspModularGapAmplitude
private abbrev w := thetaCuspModularTransverseShear

/-- Relative shear bounds the normalized full-source slope without an independent derivative premise. -/
theorem thetaCuspFullSource_compact_slope_lower {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    -(15/8 : ℝ) ≤ HTGeometry.oddCompactSourceFirst (u x) (a x) (w x) := by
  obtain ⟨hu0, hu1, ha0, ha1, hw0, hw1⟩ := thetaCuspModularState_energy_box hx
  have hrel := thetaCuspModularTransverseShear_le_fiveFourths_drift hx
  have haw := mul_le_mul_of_nonneg_left hrel (by linarith : 0 ≤ a x)
  have hau := mul_nonneg hu0 (show 0 ≤ a x-5 by linarith)
  have hu3 : 0 ≤ u x^(3 : ℕ) := pow_nonneg hu0 3
  have hf : -(2/3)*(a x*w x/8+5*u x/16) ≤
      HTGeometry.oddCompactSourceFirst (u x) (a x) (w x) := by
    unfold HTGeometry.oddCompactSourceFirst
    nlinarith only [haw, hau, hu3]
  have haw20 : a x*w x ≤ 20 := by
    have h := mul_le_mul_of_nonneg_right ha1 hw0
    nlinarith only [h, hw1]
  linarith only [hf, haw20, hu1]

/-- The complete correction admits an even polynomial lower comparison on the full energy interval. -/
theorem thetaCuspCenterCompensationSource_even_compact_lower {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    Bottcher.completedThetaProfile x^(2 : ℕ) *
      (HTGeometry.oddCompactSourceZero (u x) (a x) *
        (3*HTGeometry.oddCompactSourceZero (u x) (a x)-6/19)) ≤
      thetaCuspCenterCompensationSource x := by
  have hb := thetaCuspModularState_energy_box hx
  have hQ : 0 ≤ HTGeometry.oddCompactSourceZero (u x) (a x) := by
    unfold HTGeometry.oddCompactSourceZero
    nlinarith [hb.2.2.1, sq_nonneg (u x)]
  have hf := thetaCuspFullSource_compact_slope_lower hx
  have hmul := mul_le_mul_of_nonneg_left hf
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx.1) hQ)
  have ht : 15*x/4 ≤ (6/19 : ℝ) := by linarith [hx.2]
  have htQ := mul_le_mul_of_nonneg_right ht hQ
  have hl : HTGeometry.oddCompactSourceZero (u x) (a x)*
        (3*HTGeometry.oddCompactSourceZero (u x) (a x)-6/19) ≤
      3*HTGeometry.oddCompactSourceZero (u x) (a x)^(2 : ℕ)+
        2*x*HTGeometry.oddCompactSourceZero (u x) (a x)*
          HTGeometry.oddCompactSourceFirst (u x) (a x) (w x) := by
    nlinarith only [hmul, htQ]
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (Bottcher.completedThetaProfile x))
  unfold thetaCuspCenterCompensationSource
  rw [thetaCuspFullSource_eq_compactSourceZero, deriv_thetaCuspFullSource_eq_compactSourceFirst]
  change _ ≤ 3*(Bottcher.completedThetaProfile x*HTGeometry.oddCompactSourceZero (u x) (a x))^(2 : ℕ)+
    2*x*(Bottcher.completedThetaProfile x*HTGeometry.oddCompactSourceZero (u x) (a x))*
      (Bottcher.completedThetaProfile x*HTGeometry.oddCompactSourceFirst (u x) (a x) (w x))
  nlinarith only [hm]

end
end RHTower
