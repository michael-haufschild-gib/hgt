import GaloisForLFunctions.RHTower.ThetaCuspScaleSevenEntryErrors
import GaloisForLFunctions.HTGeometry.FirstAtomOddScaleSevenLower
import GaloisForLFunctions.HTGeometry.ScaleSevenHankelPerturbation
import GaloisForLFunctions.RHTower.ThetaCuspEffectiveOddDeterminant

/-! # Actual complete-source determinant reserves on physical scale seven -/
namespace RHTower
noncomputable section

/-- The actual first-atom normalized entries lie in the proved positive intervals. -/
theorem thetaCuspFirstAtomScaledEvenJet_interval_bounds_seven {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (8 ≤ thetaCuspFirstAtomScaledEvenJet 1 x ∧ thetaCuspFirstAtomScaledEvenJet 1 x ≤ 9) ∧
    (180 ≤ thetaCuspFirstAtomScaledEvenJet 2 x ∧ thetaCuspFirstAtomScaledEvenJet 2 x ≤ 210) ∧
    (7000 ≤ thetaCuspFirstAtomScaledEvenJet 3 x ∧ thetaCuspFirstAtomScaledEvenJet 3 x ≤ 8500) ∧
    (300000 ≤ thetaCuspFirstAtomScaledEvenJet 4 x ∧ thetaCuspFirstAtomScaledEvenJet 4 x ≤ 500000) ∧
    (20000000 ≤ thetaCuspFirstAtomScaledEvenJet 5 x ∧ thetaCuspFirstAtomScaledEvenJet 5 x ≤ 40000000) := by
  have hu := inverseScale_bounds_of_seven_le hq
  rw [thetaCuspFirstAtomScaledEvenJet_1_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_2_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_3_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_4_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_5_eq_profile_of_seven_le hq]
  exact ⟨⟨HTGeometry.firstAtomOddScaleSeven_profile1_lower hu.1 hu.2,
      (HTGeometry.firstAtomOddScaleSeven_profile1_bounds hu.1 hu.2).2⟩,
    ⟨HTGeometry.firstAtomOddScaleSeven_profile2_lower hu.1 hu.2,
      (HTGeometry.firstAtomOddScaleSeven_profile2_bounds hu.1 hu.2).2⟩,
    ⟨HTGeometry.firstAtomOddScaleSeven_profile3_lower hu.1 hu.2,
      (HTGeometry.firstAtomOddScaleSeven_profile3_bounds hu.1 hu.2).2⟩,
    ⟨HTGeometry.firstAtomOddScaleSeven_profile4_lower hu.1 hu.2,
      (HTGeometry.firstAtomOddScaleSeven_profile4_bounds hu.1 hu.2).2⟩,
    ⟨HTGeometry.firstAtomOddScaleSeven_profile5_lower hu.1 hu.2,
      (HTGeometry.firstAtomOddScaleSeven_profile5_bounds hu.1 hu.2).2⟩⟩

private theorem first_head_abs {x : ℝ} (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspFirstAtomScaledEvenJet 1 x*thetaCuspFirstAtomScaledEvenJet 3 x-
      thetaCuspFirstAtomScaledEvenJet 2 x^2| ≤ 27000 := by
  have hu := inverseScale_bounds_of_seven_le hq
  rw [thetaCuspFirstAtomScaledEvenJet_1_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_2_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_3_eq_profile_of_seven_le hq]
  exact HTGeometry.firstAtomOddScaleSeven_head_abs_le hu.1 hu.2

/-- The complete odd determinant retains seventy billion after all five literal entry errors. -/
theorem thetaCuspNativeOddHankelThreeDet_scaleSeven_normalized_lower {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    70000000000 ≤ thetaCuspNativeOddHankelThreeDet x /
      (thetaCuspSourceTerm x 1^6*thetaCuspSingleAtomReflectionScale 1 x^9) := by
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hu := inverseScale_bounds_of_seven_le hq
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_interval_bounds_seven hq
  have hd := HTGeometry.firstAtomOddScaleSeven_det_lower hu.1 hu.2
  unfold HTGeometry.firstAtomOddTailDet at hd
  rw [← thetaCuspFirstAtomScaledEvenJet_1_eq_profile_of_seven_le hq,
    ← thetaCuspFirstAtomScaledEvenJet_2_eq_profile_of_seven_le hq,
    ← thetaCuspFirstAtomScaledEvenJet_3_eq_profile_of_seven_le hq,
    ← thetaCuspFirstAtomScaledEvenJet_4_eq_profile_of_seven_le hq,
    ← thetaCuspFirstAtomScaledEvenJet_5_eq_profile_of_seven_le hq] at hd
  have he := HTGeometry.signedEvenHankelThreeDet_scaleSeven_error h1 h2 h3 h4 h5 (first_head_abs hq)
    (thetaCuspNativeScaledEvenJet_1_error_le_of_seven_le hq)
    (thetaCuspNativeScaledEvenJet_2_error_le_of_seven_le hq)
    (thetaCuspNativeScaledEvenJet_3_error_le_of_seven_le hq)
    (thetaCuspNativeScaledEvenJet_4_error_le_of_seven_le hq)
    (thetaCuspNativeScaledEvenJet_5_error_le_of_seven_le hq)
  rw [thetaCuspNativeOddHankelThreeDet_normalized hx]
  have he' := (abs_le.mp he).1
  unfold HilbertMetric.signedEvenHankelThreeDet at he' ⊢
  linarith only [hd, he']

/-- The full leading odd minor stays strictly positive and below twenty-eight thousand. -/
theorem thetaCuspNativeOddHeadDet_scaleSeven_normalized_bounds {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspNativeOddHeadDet x /
      (thetaCuspSourceTerm x 1^4*thetaCuspSingleAtomReflectionScale 1 x^4) ∧
    thetaCuspNativeOddHeadDet x /
      (thetaCuspSourceTerm x 1^4*thetaCuspSingleAtomReflectionScale 1 x^4) ≤ 28000 := by
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  refine ⟨div_pos (thetaCuspNativeOddHeadDet_pos x) (by positivity), ?_⟩
  rw [thetaCuspNativeOddHeadDet_normalized hx]
  obtain ⟨h1,h2,h3,_,_⟩ := thetaCuspFirstAtomScaledEvenJet_interval_bounds_seven hq
  exact HTGeometry.signedOddHead_scaleSeven_upper h1 h2 h3 ((abs_le.mp (first_head_abs hq)).2)
    (thetaCuspNativeScaledEvenJet_1_error_le_of_seven_le hq)
    (thetaCuspNativeScaledEvenJet_2_error_le_of_seven_le hq)
    (thetaCuspNativeScaledEvenJet_3_error_le_of_seven_le hq)

end
end RHTower
