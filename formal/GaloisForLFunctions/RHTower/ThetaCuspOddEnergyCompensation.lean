import GaloisForLFunctions.RHTower.ThetaCuspModularEnergyTube
import GaloisForLFunctions.RHTower.ThetaCuspOddCompactCompensation
import GaloisForLFunctions.RHTower.ThetaCuspScaleSevenCompensatedTail

/-!
# A larger compact interval for the compensated odd determinant

The global modular energy supplies an actual orbit tube through 8/95.
Relative shear retains positive terms in the source slope. Consequently the
existing exact determinant certificate applies on this larger interval.
-/

namespace RHTower
noncomputable section
open Set
set_option maxHeartbeats 1200000

private abbrev u := thetaCuspModularMassDrift
private abbrev a := thetaCuspModularGapAmplitude
private abbrev w := thetaCuspModularTransverseShear

private theorem lowerSource_one_le {U A W : ℝ}
    (_hU0 : 0 ≤ U) (hU1 : U ≤ 1) (hA0 : 17 ≤ A) (hA1 : A ≤ 20)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1) :
    1 ≤ HTGeometry.oddCompactLowerSource U A W := by
  have hQ : (11/16 : ℝ) ≤ HTGeometry.oddCompactSourceZero U A := by
    unfold HTGeometry.oddCompactSourceZero
    nlinarith [sq_nonneg U]
  have hAW : A*W ≤ 20 := by
    have h := mul_le_mul_of_nonneg_right hA1 hW0
    nlinarith
  have hf : (3/2 : ℝ) ≤ 3*HTGeometry.oddCompactSourceZero U A -
      (137/1000 : ℝ)*(A*W/8+5*U/16) := by linarith
  have hmul := mul_le_mul hQ hf (by norm_num : (0 : ℝ) ≤ 3/2)
    (by linarith : 0 ≤ HTGeometry.oddCompactSourceZero U A)
  unfold HTGeometry.oddCompactLowerSource
  nlinarith only [hmul]

/-- Relative shear preserves enough favorable source slope to reuse the exact compact reserve. -/
theorem thetaCuspCenterCompensationSource_energy_lower {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    Bottcher.completedThetaProfile x^2 *
      HTGeometry.oddCompactLowerSource (u x) (a x) (w x) ≤
        thetaCuspCenterCompensationSource x := by
  have hbox : 0 ≤ u x ∧ u x ≤ 1 ∧ 17 ≤ a x ∧ a x ≤ 20 ∧ 0 ≤ w x ∧ w x ≤ 1 :=
    thetaCuspModularState_energy_box hx
  obtain ⟨hu0, hu1, ha0, ha1, hw0, hw1⟩ := hbox
  have hrelative : w x ≤ (5/4)*u x := thetaCuspModularTransverseShear_le_fiveFourths_drift hx
  have hQ : 0 ≤ HTGeometry.oddCompactSourceZero (u x) (a x) := by
    unfold HTGeometry.oddCompactSourceZero
    nlinarith [sq_nonneg (u x)]
  have hloss : 0 ≤ a x*w x/8+5*u x/16 := by positivity
  have haw := mul_le_mul_of_nonneg_left hrelative (by linarith : 0 ≤ a x)
  have hau := mul_nonneg hu0 (show 0 ≤ a x-5 by linarith)
  have hu3 : 0 ≤ u x^3 := pow_nonneg hu0 3
  have hfirst : -(2/3)*(a x*w x/8+5*u x/16) ≤
      HTGeometry.oddCompactSourceFirst (u x) (a x) (w x) := by
    unfold HTGeometry.oddCompactSourceFirst
    nlinarith only [haw, hau, hu3]
  have hp := mul_le_mul_of_nonneg_left hfirst
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx.1) hQ)
  have ht : (4/3)*x ≤ (137/1000 : ℝ) := by linarith [hx.2]
  have htq := mul_le_mul_of_nonneg_right ht
    (mul_nonneg hQ hloss)
  have hb : HTGeometry.oddCompactLowerSource (u x) (a x) (w x) ≤
      3*(HTGeometry.oddCompactSourceZero (u x) (a x))^2+
      2*x*HTGeometry.oddCompactSourceZero (u x) (a x)*
        HTGeometry.oddCompactSourceFirst (u x) (a x) (w x) := by
    unfold HTGeometry.oddCompactLowerSource
    nlinarith only [hp, htq]
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (Bottcher.completedThetaProfile x))
  unfold thetaCuspCenterCompensationSource
  rw [thetaCuspFullSource_eq_compactSourceZero, deriv_thetaCuspFullSource_eq_compactSourceFirst]
  change Bottcher.completedThetaProfile x^2*
    HTGeometry.oddCompactLowerSource (u x) (a x) (w x) ≤
    3*(Bottcher.completedThetaProfile x*HTGeometry.oddCompactSourceZero (u x) (a x))^2+
    2*x*(Bottcher.completedThetaProfile x*HTGeometry.oddCompactSourceZero (u x) (a x))*
      (Bottcher.completedThetaProfile x*HTGeometry.oddCompactSourceFirst (u x) (a x) (w x))
  nlinarith only [hm]

/-- The complete correction retains one squared mass on the enlarged compact interval. -/
theorem thetaCuspCenterCompensationSource_ge_mass_sq_on_energy_interval {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    Bottcher.completedThetaProfile x^2 ≤ thetaCuspCenterCompensationSource x := by
  have hbox : 0 ≤ u x ∧ u x ≤ 1 ∧ 17 ≤ a x ∧ a x ≤ 20 ∧ 0 ≤ w x ∧ w x ≤ 1 :=
    thetaCuspModularState_energy_box hx
  obtain ⟨hu0, hu1, ha0, ha1, hw0, hw1⟩ := hbox
  have hl := lowerSource_one_le hu0 hu1 ha0 ha1 hw0 hw1
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (Bottcher.completedThetaProfile x))
  have hs := thetaCuspCenterCompensationSource_energy_lower hx
  nlinarith only [hm, hs]

/-- A fixed positive reserve for every coefficient at least one billion, through 8/95. -/
theorem thetaCuspNativeOddCompensatedDet_energy_lower {C x : ℝ}
    (hC : 1000000000 ≤ C) (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    Bottcher.completedThetaProfile x^6*100000000000000 ≤
      thetaCuspNativeOddCompensatedDet C x := by
  have hbox : 0 ≤ u x ∧ u x ≤ 1 ∧ 17 ≤ a x ∧ a x ≤ 20 ∧ 0 ≤ w x ∧ w x ≤ 1 :=
    thetaCuspModularState_energy_box hx
  obtain ⟨hu0, hu1, ha0, ha1, hw0, hw1⟩ := hbox
  have hp := HTGeometry.oddCompactDet_corrected_lower hu0 hu1 ha0 ha1 hw0 hw1
  have hm := mul_le_mul_of_nonneg_left hp
    (pow_nonneg (thetaCuspCompletedThetaProfile_pos x).le 6)
  have hg := thetaCuspCenterCompensationSource_energy_lower hx
  have hd := thetaCuspNativeOddHeadDet_pos x
  have hcg := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ (1000000000 : ℝ)*thetaCuspNativeOddHeadDet x by positivity)
  have hfixed : Bottcher.completedThetaProfile x^6*100000000000000 ≤
      thetaCuspNativeOddCompensatedDet 1000000000 x := by
    unfold thetaCuspNativeOddCompensatedDet
    rw [thetaCuspNativeOddHankelThreeDet_eq_compactPolynomial]
    rw [thetaCuspNativeOddHeadDet_eq_compactPolynomial] at hcg ⊢
    change _ ≤ Bottcher.completedThetaProfile x^6*
      HTGeometry.oddCompactDet (u x) (a x) (w x)+_
    change (1000000000*(Bottcher.completedThetaProfile x^4*HTGeometry.oddCompactHead (u x) (a x) (w x)))*
      (Bottcher.completedThetaProfile x^2*HTGeometry.oddCompactLowerSource (u x) (a x) (w x)) ≤
      (1000000000*(Bottcher.completedThetaProfile x^4*HTGeometry.oddCompactHead (u x) (a x) (w x)))*
        thetaCuspCenterCompensationSource x at hcg
    change _ ≤ Bottcher.completedThetaProfile x^6*HTGeometry.oddCompactDet (u x) (a x) (w x)+
      1000000000*(Bottcher.completedThetaProfile x^4*HTGeometry.oddCompactHead (u x) (a x) (w x))*
        thetaCuspCenterCompensationSource x
    nlinarith only [hm, hcg]
  have hG : 0 ≤ thetaCuspCenterCompensationSource x :=
    (sq_nonneg (Bottcher.completedThetaProfile x)).trans
      (thetaCuspCenterCompensationSource_ge_mass_sq_on_energy_interval hx)
  have hmono := mul_le_mul_of_nonneg_right hC (mul_nonneg hd.le hG)
  apply hfixed.trans
  unfold thetaCuspNativeOddCompensatedDet
  nlinarith only [hmono]

/-- Every coefficient at least one billion repairs all centers through 8/95. -/
theorem thetaCuspNativeOddCompensatedDet_pos_on_energy_interval {C x : ℝ}
    (hC : 1000000000 ≤ C) (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    0 < thetaCuspNativeOddCompensatedDet C x := by
  exact (mul_pos (pow_pos (thetaCuspCompletedThetaProfile_pos x) 6)
    (by norm_num : (0 : ℝ) < 100000000000000)).trans_le
      (thetaCuspNativeOddCompensatedDet_energy_lower hC hx)

/-- Unconditional canonical positivity outside the reduced compact gap. -/
theorem thetaCuspNativeOddCanonicalCompensatedDet_pos_outside_energy_gap :
    ∀ x : ℝ, 0 ≤ x → (x ≤ 8/95 ∨ 7/16 ≤ x) →
      0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x := by
  intro x hx hregion
  rcases hregion with hleft | hright
  · exact thetaCuspNativeOddCompensatedDet_pos_on_energy_interval
      thetaCuspNativeOddCompensationCoefficient_bounds.1.le ⟨hx, hleft⟩
  · exact thetaCuspNativeOddCanonicalCompensatedDet_pos_on_scaleSeven_tail x hright

/-- The corrected weighted odd determinant is positive at every aperture through r=16/95. -/
theorem thetaCuspCenterCorrectedOddDet_pos_on_energy_interval {a C r : ℝ}
    (ha : 0 < a) (hC : 1000000000 ≤ C) (hr : 0 < r) (hr1 : r ≤ 16/95) :
    0 < thetaCuspCenterCorrectedOddDet a C r := by
  have hs := thetaCuspNativeOddCompensatedDet_pos_on_energy_interval hC
    (show r/2 ∈ Icc (0 : ℝ) (8/95) from ⟨by linarith, by linarith⟩)
  have hw : 0 < r*Real.sinh (a*r) := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  exact (mul_pos (pow_pos hw 3) hs).trans_le
    (thetaCuspCenterCorrectedOddDet_lower ha.le (by linarith) hr.le)

end
end RHTower
