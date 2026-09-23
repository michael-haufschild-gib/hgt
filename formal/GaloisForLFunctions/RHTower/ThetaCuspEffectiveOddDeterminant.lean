import GaloisForLFunctions.RHTower.ThetaCuspEffectiveFirstAtomProfiles
import GaloisForLFunctions.HTGeometry.HankelThreePerturbation

/-! # Effective native odd determinant and leading-minor bounds -/
namespace RHTower
noncomputable section

/-- The exact Gaussian normalization of the native odd determinant. -/
theorem thetaCuspNativeOddHankelThreeDet_normalized {x : ℝ} (hx : 0 < x) :
    thetaCuspNativeOddHankelThreeDet x /
      (thetaCuspSourceTerm x 1^(6 : ℕ) * thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)) =
    HilbertMetric.signedEvenHankelThreeDet
      (thetaCuspNativeScaledEvenJet 1 x) (thetaCuspNativeScaledEvenJet 2 x)
      (thetaCuspNativeScaledEvenJet 3 x) (thetaCuspNativeScaledEvenJet 4 x)
      (thetaCuspNativeScaledEvenJet 5 x) := by
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale; positivity
  unfold thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
    thetaCuspNativeScaledEvenJet
  norm_num only [Nat.reduceMul, pow_one, neg_pow, one_pow]
  field_simp
  <;> ring

/-- The exact Gaussian normalization of the leading odd minor. -/
theorem thetaCuspNativeOddHeadDet_normalized {x : ℝ} (hx : 0 < x) :
    thetaCuspNativeOddHeadDet x /
      (thetaCuspSourceTerm x 1^(4 : ℕ) * thetaCuspSingleAtomReflectionScale 1 x^(4 : ℕ)) =
      thetaCuspNativeScaledEvenJet 1 x*thetaCuspNativeScaledEvenJet 3 x -
        thetaCuspNativeScaledEvenJet 2 x^(2 : ℕ) := by
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale; positivity
  unfold thetaCuspNativeOddHeadDet thetaCuspNativeScaledEvenJet
  norm_num only [Nat.reduceMul, pow_one, neg_pow, one_pow]
  field_simp
  <;> ring

private theorem transfer_entry_bound {a b : ℝ} (hb : |b| ≤ 100000000)
    (he : |a-b| ≤ 1/(10 : ℝ)^(10 : ℕ)) : |a| ≤ 200000000 := by
  have h := abs_add_le (a-b) b
  rw [sub_add_cancel] at h
  linarith

/-- On scale thirty and beyond, the normalized complete-source determinant has a fixed reserve. -/
theorem thetaCuspNativeOddHankelThreeDet_normalized_lower {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    49000000000 ≤ thetaCuspNativeOddHankelThreeDet x /
      (thetaCuspSourceTerm x 1^(6 : ℕ) * thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)) := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hu := inverseScale_bounds_of_thirty_le hq
  have hb := HTGeometry.firstAtomOddTailProfiles_bounds hu.1 hu.2
  have hd := HTGeometry.firstAtomOddTailDet_lower hu.1 hu.2
  have hp1 := thetaCuspFirstAtomScaledEvenJet_1_eq_profile hq
  have hp2 := thetaCuspFirstAtomScaledEvenJet_2_eq_profile hq
  have hp3 := thetaCuspFirstAtomScaledEvenJet_3_eq_profile hq
  have hp4 := thetaCuspFirstAtomScaledEvenJet_4_eq_profile hq
  have hp5 := thetaCuspFirstAtomScaledEvenJet_5_eq_profile hq
  rw [← hp1, ← hp2, ← hp3, ← hp4, ← hp5] at hb
  unfold HTGeometry.firstAtomOddTailDet at hd
  rw [← hp1, ← hp2, ← hp3, ← hp4, ← hp5] at hd
  rcases hb with ⟨h1,h2,h3,h4,h5,_,_⟩
  have e1 := abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten (k := 1) (by norm_num) hq
  have e2 := abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten (k := 2) (by norm_num) hq
  have e3 := abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten (k := 3) (by norm_num) hq
  have e4 := abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten (k := 4) (by norm_num) hq
  have e5 := abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten (k := 5) (by norm_num) hq
  have herr := HTGeometry.signedEvenHankelThreeDet_error_le
    (M := 200000000) (δ := 1/(10 : ℝ)^(10 : ℕ)) (by norm_num) (by positivity)
    ⟨transfer_entry_bound h1 e1, transfer_entry_bound h2 e2, transfer_entry_bound h3 e3,
      transfer_entry_bound h4 e4, transfer_entry_bound h5 e5⟩
    ⟨by linarith [h1], by linarith [h2], by linarith [h3], by linarith [h4], by linarith [h5]⟩
    ⟨e1,e2,e3,e4,e5⟩
  rw [thetaCuspNativeOddHankelThreeDet_normalized hx]
  have herr' := (abs_le.mp herr).1
  unfold HilbertMetric.signedEvenHankelThreeDet at *
  linarith only [herr', hd]

/-- The complete leading minor stays below an explicit Gaussian-scale ceiling. -/
theorem thetaCuspNativeOddHeadDet_normalized_bounds {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspNativeOddHeadDet x /
      (thetaCuspSourceTerm x 1^(4 : ℕ) * thetaCuspSingleAtomReflectionScale 1 x^(4 : ℕ)) ∧
    thetaCuspNativeOddHeadDet x /
      (thetaCuspSourceTerm x 1^(4 : ℕ) * thetaCuspSingleAtomReflectionScale 1 x^(4 : ℕ)) ≤ 100000 := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  refine ⟨div_pos (thetaCuspNativeOddHeadDet_pos x) (by positivity), ?_⟩
  rw [thetaCuspNativeOddHeadDet_normalized hx]
  have hu := inverseScale_bounds_of_thirty_le hq
  obtain ⟨_,_,_,_,_,h1,h3⟩ := HTGeometry.firstAtomOddTailProfiles_bounds hu.1 hu.2
  rw [← thetaCuspFirstAtomScaledEvenJet_1_eq_profile hq] at h1
  rw [← thetaCuspFirstAtomScaledEvenJet_3_eq_profile hq] at h3
  have e1 := (abs_le.mp (abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten
    (k := 1) (by norm_num) hq)).2
  have e3 := (abs_le.mp (abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten
    (k := 3) (by norm_num) hq)).2
  have ha : 0 < thetaCuspNativeScaledEvenJet 1 x := by
    unfold thetaCuspNativeScaledEvenJet
    norm_num only [Nat.reduceMul, pow_one, neg_mul, one_mul]
    exact div_pos (thetaCuspNativeOddHankelThree_head_pos x).1 (by positivity)
  have ha10 : thetaCuspNativeScaledEvenJet 1 x ≤ 10 := by linarith
  have hc10000 : thetaCuspNativeScaledEvenJet 3 x ≤ 10000 := by linarith
  have hm := mul_le_mul_of_nonneg_left hc10000 ha.le
  nlinarith [sq_nonneg (thetaCuspNativeScaledEvenJet 2 x)]

end
end RHTower
