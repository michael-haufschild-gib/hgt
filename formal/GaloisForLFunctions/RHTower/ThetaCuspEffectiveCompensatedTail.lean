import GaloisForLFunctions.RHTower.ThetaCuspEffectiveOddDeterminant
import GaloisForLFunctions.RHTower.ThetaCuspEffectiveCompensationSource
import GaloisForLFunctions.RHTower.ThetaCuspOddCompactCompensation

/-!
# An explicit compensated odd tail and a fixed remaining compact interval

Every coefficient in [0, 3e9] gives a positive compensated determinant on q >= 30,
hence on x >= 6/5. Together with the explicit seam interval, the canonical
coefficient is now positive outside the fixed compact gap (137/2000, 6/5).
-/
namespace RHTower
noncomputable section

/-- The determinant reserve exceeds the entire adverse compensation on the explicit scale ray. -/
theorem thetaCuspNativeOddCompensatedDet_effective_normalized_lower {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000)
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    20000000000 ≤ thetaCuspNativeOddCompensatedDet C x /
      (thetaCuspSourceTerm x 1^6 * thetaCuspSingleAtomReflectionScale 1 x^9) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let H := thetaCuspNativeOddHankelThreeDet x/(f^6*q^9)
  let D := thetaCuspNativeOddHeadDet x/(f^4*q^4)
  let G := thetaCuspCenterCompensationSource x/(f^2*q^5)
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < q := by dsimp [q]; linarith
  have hH : 49000000000 ≤ H := thetaCuspNativeOddHankelThreeDet_normalized_lower hq
  have hD : 0 < D ∧ D ≤ 100000 := thetaCuspNativeOddHeadDet_normalized_bounds hq
  have hG : -(2 : ℝ)/30^3 ≤ G := thetaCuspCenterCompensationSource_normalized_lower hq
  have hCD := mul_le_mul hC1 hD.2 hD.1.le (by norm_num : (0 : ℝ) ≤ 3000000000)
  have hCG := mul_le_mul_of_nonneg_left hG (mul_nonneg hC0 hD.1.le)
  have heq : thetaCuspNativeOddCompensatedDet C x/(f^6*q^9) = H+C*D*G := by
    dsimp [H, D, G]
    unfold thetaCuspNativeOddCompensatedDet
    field_simp
    <;> ring
  change 20000000000 ≤ thetaCuspNativeOddCompensatedDet C x/(f^6*q^9)
  rw [heq]
  nlinarith only [hH, hCD, hCG]

/-- The compensated native determinant is strictly positive throughout the explicit scale ray. -/
theorem thetaCuspNativeOddCompensatedDet_pos_of_thirty_le {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000)
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspNativeOddCompensatedDet C x := by
  have hl := thetaCuspNativeOddCompensatedDet_effective_normalized_lower hC0 hC1 hq
  have hpos : 0 < thetaCuspNativeOddCompensatedDet C x /
      (thetaCuspSourceTerm x 1^6*thetaCuspSingleAtomReflectionScale 1 x^9) := by linarith
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hh := (lt_div_iff₀ (by positivity : 0 <
    thetaCuspSourceTerm x 1^6*thetaCuspSingleAtomReflectionScale 1 x^9)).mp hpos
  simpa only [zero_mul] using hh

/-- The rational center endpoint six fifths lies beyond physical scale thirty. -/
theorem thirty_le_firstAtomScale_of_six_fifths_le {x : ℝ} (hx : 6/5 ≤ x) :
    30 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have h1 : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (27/10 : ℝ)^2 ≤ Real.exp 2 := by
    have h := pow_le_pow_left₀ (by norm_num) h1 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hr : (7/5 : ℝ) ≤ Real.exp (2/5) := by linarith [Real.add_one_le_exp (2/5)]
  have hm := mul_le_mul h2 hr (by norm_num : (0 : ℝ) ≤ 7/5) (Real.exp_pos 2).le
  rw [← Real.exp_add] at hm
  norm_num at hm
  have hxexp := Real.exp_le_exp.mpr (show (12/5 : ℝ) ≤ 2*x by linarith)
  have hp := mul_le_mul_of_nonneg_left (hm.trans hxexp) Real.pi_pos.le
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
  nlinarith [Real.pi_gt_three]

/-- A fully explicit cofinal ray works uniformly for the entire bounded coefficient family. -/
theorem thetaCuspNativeOddCompensatedDet_pos_on_effective_tail {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000) (hx : 6/5 ≤ x) :
    0 < thetaCuspNativeOddCompensatedDet C x :=
  thetaCuspNativeOddCompensatedDet_pos_of_thirty_le hC0 hC1
    (thirty_le_firstAtomScale_of_six_fifths_le hx)

/-- Closed explicit tail positivity for the actual source-selected coefficient. -/
theorem thetaCuspNativeOddCanonicalCompensatedDet_pos_on_effective_tail :
    ∀ x : ℝ, 6/5 ≤ x →
      0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x := by
  intro x hx
  exact thetaCuspNativeOddCompensatedDet_pos_on_effective_tail
    thetaCuspNativeOddCompensationCoefficient_pos.le
    thetaCuspNativeOddCompensationCoefficient_bounds.2.le hx

/-- The canonical source sign is established on explicit initial and final center intervals. -/
theorem thetaCuspNativeOddCanonicalCompensatedDet_pos_outside_gap :
    ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) (137/2000) ∪ Set.Ici (6/5 : ℝ) →
      0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x := by
  intro x hx
  rcases hx with hx | hx
  · exact thetaCuspNativeOddCanonicalCompensatedDet_pos_on_compact x hx
  · exact thetaCuspNativeOddCanonicalCompensatedDet_pos_on_effective_tail x hx

/-- Every positive aperture has a positive corrected weighted determinant on the explicit tail. -/
theorem thetaCuspCenterCorrectedOddDet_pos_on_effective_tail {a C r : ℝ}
    (ha : 0 < a) (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000) (hr : 12/5 ≤ r) :
    0 < thetaCuspCenterCorrectedOddDet a C r := by
  have hr0 : 0 < r := by linarith
  have hsource := thetaCuspNativeOddCompensatedDet_pos_on_effective_tail hC0 hC1
    (show (6/5 : ℝ) ≤ r/2 by linarith)
  have hw : 0 < r*Real.sinh (a*r) :=
    mul_pos hr0 (Real.sinh_pos_iff.mpr (mul_pos ha hr0))
  exact (mul_pos (pow_pos hw 3) hsource).trans_le
    (thetaCuspCenterCorrectedOddDet_lower ha.le hC0 hr0.le)

end
end RHTower
