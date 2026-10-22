import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleOddDeterminant
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleCompensationBounds

/-! # Complete compensated determinant positivity throughout the middle interval -/
namespace RHTower
noncomputable section

/-- Positive compensation preserves the half-billion lower-middle determinant reserve. -/
theorem thetaCuspNativeOddCompensatedDet_pos_on_lower_middle {C x : ℝ}
    (hC : 0 ≤ C) (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    0 < thetaCuspNativeOddCompensatedDet C x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq0
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hH := thetaCuspNativeOddHankelThreeDet_lower_middle_normalized_lower hq0 hq1
  have hH0 : 0 < thetaCuspNativeOddHankelThreeDet x := by
    have hpos : 0 < thetaCuspNativeOddHankelThreeDet x /
        (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)) := by linarith
    have hh := (lt_div_iff₀ (by positivity : 0 <
      thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ))).mp hpos
    simpa only [zero_mul] using hh
  have hG := thetaCuspCenterCompensationSource_pos_on_scale_five hq0 hq1
  have hD := thetaCuspNativeOddHeadDet_pos x
  unfold thetaCuspNativeOddCompensatedDet
  exact add_pos_of_pos_of_nonneg hH0 (by positivity)

/-- The complete upper-middle reserve exceeds every permitted adverse correction by thirty billion. -/
theorem thetaCuspNativeOddCompensatedDet_upper_middle_normalized_lower {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000)
    (hq0 : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    30000000000 ≤ thetaCuspNativeOddCompensatedDet C x /
      (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let H := thetaCuspNativeOddHankelThreeDet x/(f^(6 : ℕ)*q^(9 : ℕ))
  let D := thetaCuspNativeOddHeadDet x/(f^(4 : ℕ)*q^(4 : ℕ))
  let G := thetaCuspCenterCompensationSource x/(f^(2 : ℕ)*q^(5 : ℕ))
  have hx := thetaCusp_pos_of_thirtySevenTenths_le (x := x) (by linarith)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < q := by dsimp [q]; linarith
  have hH : 70500000000 ≤ H := thetaCuspNativeOddHankelThreeDet_upper_middle_normalized_lower hq0 hq1
  have hD : 0 < D ∧ D ≤ 33100 := thetaCuspNativeOddHeadDet_upper_middle_normalized_bounds hq0 hq1
  have hG : -(1 : ℝ)/2500 ≤ G := thetaCuspCenterCompensationSource_middle_normalized_lower
    (by linarith) hq1
  have hCD := mul_le_mul hC1 hD.2 hD.1.le (by norm_num : (0 : ℝ) ≤ 3000000000)
  have hCG := mul_le_mul_of_nonneg_left hG (mul_nonneg hC0 hD.1.le)
  have heq : thetaCuspNativeOddCompensatedDet C x/(f^(6 : ℕ)*q^(9 : ℕ)) = H+C*D*G := by
    dsimp [H,D,G]
    unfold thetaCuspNativeOddCompensatedDet
    field_simp
  change 30000000000 ≤ thetaCuspNativeOddCompensatedDet C x/(f^(6 : ℕ)*q^(9 : ℕ))
  rw [heq]
  nlinarith only [hH, hCD, hCG]

/-- Every allowed coefficient gives strict complete-source positivity on the whole middle interval. -/
theorem thetaCuspNativeOddCompensatedDet_pos_on_middle {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000)
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    0 < thetaCuspNativeOddCompensatedDet C x := by
  by_cases h5 : thetaCuspSingleAtomReflectionScale 1 x ≤ 5
  · exact thetaCuspNativeOddCompensatedDet_pos_on_lower_middle hC0 hq0 h5
  · have hl := thetaCuspNativeOddCompensatedDet_upper_middle_normalized_lower hC0 hC1
      (le_of_not_ge h5) hq1
    have hx := thetaCusp_pos_of_thirtySevenTenths_le hq0
    have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
    have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
    have hpos : 0 < thetaCuspNativeOddCompensatedDet C x /
        (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)) := by linarith
    have hh := (lt_div_iff₀ (by positivity : 0 <
      thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ))).mp hpos
    simpa only [zero_mul] using hh

end
end RHTower
