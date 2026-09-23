import GaloisForLFunctions.RHTower.ThetaCuspScaleSevenOddDeterminant
import GaloisForLFunctions.RHTower.ThetaCuspScaleSevenCompensationSource
import GaloisForLFunctions.RHTower.ThetaCuspOddCompactCompensation

/-!
# Compensated odd positivity from physical scale seven

The factorized source-error estimate and exact cofactor comparison give a
uniform compensated margin on q >= 7, hence on x >= 7/16. The canonical
source comparison remains open only on the fixed gap (137/2000, 7/16).
-/
namespace RHTower
noncomputable section

/-- The source-specific odd determinant reserve absorbs every allowed adverse correction. -/
theorem thetaCuspNativeOddCompensatedDet_scaleSeven_normalized_lower {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000)
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    5000000000 ≤ thetaCuspNativeOddCompensatedDet C x /
      (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let H := thetaCuspNativeOddHankelThreeDet x/(f^(6 : ℕ)*q^(9 : ℕ))
  let D := thetaCuspNativeOddHeadDet x/(f^(4 : ℕ)*q^(4 : ℕ))
  let G := thetaCuspCenterCompensationSource x/(f^(2 : ℕ)*q^(5 : ℕ))
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < q := by dsimp [q]; linarith
  have hH : 70000000000 ≤ H := thetaCuspNativeOddHankelThreeDet_scaleSeven_normalized_lower hq
  have hD : 0 < D ∧ D ≤ 28000 := thetaCuspNativeOddHeadDet_scaleSeven_normalized_bounds hq
  have hG : -(13/50 : ℝ)/7^(3 : ℕ) ≤ G := thetaCuspCenterCompensationSource_scaleSeven_normalized_lower hq
  have hCD := mul_le_mul hC1 hD.2 hD.1.le (by norm_num : (0 : ℝ) ≤ 3000000000)
  have hCG := mul_le_mul_of_nonneg_left hG (mul_nonneg hC0 hD.1.le)
  have heq : thetaCuspNativeOddCompensatedDet C x/(f^(6 : ℕ)*q^(9 : ℕ)) = H+C*D*G := by
    dsimp [H,D,G]
    unfold thetaCuspNativeOddCompensatedDet
    field_simp
  change 5000000000 ≤ thetaCuspNativeOddCompensatedDet C x/(f^(6 : ℕ)*q^(9 : ℕ))
  rw [heq]
  nlinarith only [hH, hCD, hCG]

/-- Strict complete-source compensated positivity on the entire scale-seven ray. -/
theorem thetaCuspNativeOddCompensatedDet_pos_of_seven_le {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000)
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspNativeOddCompensatedDet C x := by
  have hl := thetaCuspNativeOddCompensatedDet_scaleSeven_normalized_lower hC0 hC1 hq
  have hpos : 0 < thetaCuspNativeOddCompensatedDet C x /
      (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)) := by linarith
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hh := (lt_div_iff₀ (by positivity : 0 <
    thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ))).mp hpos
  simpa only [zero_mul] using hh

/-- A rational center endpoint lies beyond scale seven by the global exponential comparison. -/
theorem seven_le_firstAtomScale_of_seven_sixteenths_le {x : ℝ} (hx : 7/16 ≤ x) :
    7 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have h := sixteen_mul_center_le_firstAtomScale (x := x) (by linarith)
  linarith

/-- The complete coefficient family has a positive explicit tail starting at seven sixteenths. -/
theorem thetaCuspNativeOddCompensatedDet_pos_on_scaleSeven_tail {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000) (hx : 7/16 ≤ x) :
    0 < thetaCuspNativeOddCompensatedDet C x :=
  thetaCuspNativeOddCompensatedDet_pos_of_seven_le hC0 hC1
    (seven_le_firstAtomScale_of_seven_sixteenths_le hx)

/-- Closed positivity of the actual canonical coefficient on the enlarged explicit tail. -/
theorem thetaCuspNativeOddCanonicalCompensatedDet_pos_on_scaleSeven_tail :
    ∀ x : ℝ, 7/16 ≤ x →
      0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x := by
  intro x hx
  exact thetaCuspNativeOddCompensatedDet_pos_on_scaleSeven_tail
    thetaCuspNativeOddCompensationCoefficient_pos.le
    thetaCuspNativeOddCompensationCoefficient_bounds.2.le hx

/-- Canonical positivity is proved outside the remaining fixed compact gap. -/
theorem thetaCuspNativeOddCanonicalCompensatedDet_pos_outside_scaleSeven_gap :
    ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) (137/2000) ∪ Set.Ici (7/16 : ℝ) →
      0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x := by
  intro x hx
  rcases hx with hx | hx
  · exact thetaCuspNativeOddCanonicalCompensatedDet_pos_on_compact x hx
  · exact thetaCuspNativeOddCanonicalCompensatedDet_pos_on_scaleSeven_tail x hx

/-- The actual corrected weighted determinant is positive on the enlarged tail at every aperture. -/
theorem thetaCuspCenterCorrectedOddDet_pos_on_scaleSeven_tail {a C r : ℝ}
    (ha : 0 < a) (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000) (hr : 7/8 ≤ r) :
    0 < thetaCuspCenterCorrectedOddDet a C r := by
  have hr0 : 0 < r := by linarith
  have hsource := thetaCuspNativeOddCompensatedDet_pos_on_scaleSeven_tail hC0 hC1
    (show (7/16 : ℝ) ≤ r/2 by linarith)
  have hw : 0 < r*Real.sinh (a*r) :=
    mul_pos hr0 (Real.sinh_pos_iff.mpr (mul_pos ha hr0))
  exact (mul_pos (pow_pos hw 3) hsource).trans_le
    (thetaCuspCenterCorrectedOddDet_lower ha.le hC0 hr0.le)

end
end RHTower
