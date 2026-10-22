import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleEntryErrors
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomOddReserves
import GaloisForLFunctions.HTGeometry.MiddleHankelPerturbation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveOddDeterminant

/-! # Complete source odd determinant reserves across the middle interval -/
namespace RHTower
noncomputable section

/-- Actual retained entries satisfy every interval used by the cofactor perturbation theorem. -/
theorem thetaCuspTwoAtomScaledEvenJet_interval_bounds_middle {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    (8 ≤ thetaCuspTwoAtomScaledEvenJet 1 x ∧ thetaCuspTwoAtomScaledEvenJet 1 x ≤ 11) ∧
    (180 ≤ thetaCuspTwoAtomScaledEvenJet 2 x ∧ thetaCuspTwoAtomScaledEvenJet 2 x ≤ 310) ∧
    (100 ≤ thetaCuspTwoAtomScaledEvenJet 3 x ∧ thetaCuspTwoAtomScaledEvenJet 3 x ≤ 14000) ∧
    (1000 ≤ thetaCuspTwoAtomScaledEvenJet 4 x ∧ thetaCuspTwoAtomScaledEvenJet 4 x ≤ 800000) ∧
    (1000000 ≤ thetaCuspTwoAtomScaledEvenJet 5 x ∧ thetaCuspTwoAtomScaledEvenJet 5 x ≤ 55000000) := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq0
  have hz := thetaCuspTwoAtom_middle_envelope_admission hq0
  rw [thetaCuspTwoAtomScaledEvenJet_1_eq_profile hx,
    thetaCuspTwoAtomScaledEvenJet_2_eq_profile hx,
    thetaCuspTwoAtomScaledEvenJet_3_eq_profile hx,
    thetaCuspTwoAtomScaledEvenJet_4_eq_profile hx,
    thetaCuspTwoAtomScaledEvenJet_5_eq_profile hx]
  exact ⟨HTGeometry.twoAtomOddProfile1_middle_bounds hq0 hq1 (Real.exp_pos _).le hz,
    HTGeometry.twoAtomOddProfile2_middle_bounds hq0 hq1 (Real.exp_pos _).le hz,
    HTGeometry.twoAtomOddProfile3_middle_bounds hq0 hq1 (Real.exp_pos _).le hz,
    HTGeometry.twoAtomOddProfile4_middle_bounds hq0 hq1 (Real.exp_pos _).le hz,
    HTGeometry.twoAtomOddProfile5_middle_bounds hq0 hq1 (Real.exp_pos _).le hz⟩

/-- The actual retained leading cofactor obeys the uniform absolute middle bound. -/
theorem thetaCuspTwoAtomOddHeadNormalized_abs_le_middle {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    |thetaCuspTwoAtomOddHeadNormalized x| ≤ 55000 := by
  rw [thetaCuspTwoAtomOddHeadNormalized_eq (thetaCusp_pos_of_thirtySevenTenths_le hq0)]
  have h := HTGeometry.twoAtomOddHead_middle_bounds hq0 hq1 (Real.exp_pos _).le
    (thetaCuspTwoAtom_middle_envelope_admission hq0)
  rw [abs_of_nonneg h.1]
  exact h.2

/-- The determinant of the complete source differs from the retained determinant by at most 14.5 billion. -/
theorem thetaCuspNativeOddHankelThreeDet_middle_normalized_error {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    |thetaCuspNativeOddHankelThreeDet x /
      (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ))-
        thetaCuspTwoAtomOddDetNormalized x| ≤ 14500000000 := by
  rw [thetaCuspNativeOddHankelThreeDet_normalized (thetaCusp_pos_of_thirtySevenTenths_le hq0)]
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspTwoAtomScaledEvenJet_interval_bounds_middle hq0 hq1
  exact HTGeometry.signedEvenHankelThreeDet_middle_error h1 h2 h3 h4 h5
    (thetaCuspTwoAtomOddHeadNormalized_abs_le_middle hq0 hq1)
    (thetaCuspNativeScaledEvenJet_1_two_error_le_middle hq0 hq1)
    (thetaCuspNativeScaledEvenJet_2_two_error_le_middle hq0 hq1)
    (thetaCuspNativeScaledEvenJet_3_two_error_le_middle hq0 hq1)
    (thetaCuspNativeScaledEvenJet_4_two_error_le_middle hq0 hq1)
    (thetaCuspNativeScaledEvenJet_5_two_error_le_middle hq0 hq1)

/-- Complete-source determinant reserve on physical scale [37/10,5]. -/
theorem thetaCuspNativeOddHankelThreeDet_lower_middle_normalized_lower {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    500000000 ≤ thetaCuspNativeOddHankelThreeDet x /
      (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)) := by
  have he := thetaCuspNativeOddHankelThreeDet_middle_normalized_error (x := x) (by linarith) (by linarith)
  have hl := thetaCuspTwoAtomOddDetNormalized_lower_middle hq0 hq1
  have he' := (abs_le.mp he).1
  linarith only [hl, he']

/-- Complete-source determinant reserve on physical scale [5,7]. -/
theorem thetaCuspNativeOddHankelThreeDet_upper_middle_normalized_lower {x : ℝ}
    (hq0 : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    70500000000 ≤ thetaCuspNativeOddHankelThreeDet x /
      (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)) := by
  have he := thetaCuspNativeOddHankelThreeDet_middle_normalized_error (x := x) (by linarith) (by linarith)
  have hl := thetaCuspTwoAtomOddDetNormalized_upper_middle hq0 hq1
  have he' := (abs_le.mp he).1
  linarith only [hl, he']

/-- The complete leading odd minor stays positive and below 33100 on the upper middle interval. -/
theorem thetaCuspNativeOddHeadDet_upper_middle_normalized_bounds {x : ℝ}
    (hq0 : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    0 < thetaCuspNativeOddHeadDet x /
      (thetaCuspSourceTerm x 1^(4 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(4 : ℕ)) ∧
    thetaCuspNativeOddHeadDet x /
      (thetaCuspSourceTerm x 1^(4 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(4 : ℕ)) ≤ 33100 := by
  have hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  refine ⟨div_pos (thetaCuspNativeOddHeadDet_pos x) (by positivity), ?_⟩
  rw [thetaCuspNativeOddHeadDet_normalized hx]
  obtain ⟨h1,h2,h3,_,_⟩ := thetaCuspTwoAtomScaledEvenJet_interval_bounds_middle hq hq1
  exact HTGeometry.signedOddHead_middle_upper h1 h2 h3
    (thetaCuspTwoAtomOddHeadNormalized_upper_middle hq0 hq1)
    (thetaCuspNativeScaledEvenJet_1_two_error_le_middle hq hq1)
    (thetaCuspNativeScaledEvenJet_2_two_error_le_middle hq hq1)
    (thetaCuspNativeScaledEvenJet_3_two_error_le_middle hq hq1)

end
end RHTower
