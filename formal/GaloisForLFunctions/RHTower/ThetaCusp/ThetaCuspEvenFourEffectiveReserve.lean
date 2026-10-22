import GaloisForLFunctions.HTGeometry.FirstAtomEvenTailReserve
import GaloisForLFunctions.HTGeometry.HankelFourPerturbation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourEffectiveErrors
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveFirstAtomProfiles

/-! # The exact first-atom reserve transferred to the complete even rank-four source -/
namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- Exact inverse-scale formula for the previously unbounded twelfth entry. -/
theorem thetaCuspFirstAtomScaledEvenJet_six_eq_profile {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 6 x =
      HTGeometry.firstAtomEvenTailProfile 6 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by nlinarith
  have hu := inverseScale_bounds_of_thirty_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/30 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_12, thetaCuspSourceTerm_one_eq_scale_profile]
  norm_num [HTGeometry.firstAtomEvenTailProfile]
  dsimp [HTGeometry.firstAtomEvenTailNumerator6, HTGeometry.firstAtomOddTailDenominator]
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  ring

/-- Every balanced entry uses the actual first atom in its proved rational profile. -/
theorem thetaCuspFirstAtomScaledEvenJet_fin_eq_profile {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
    thetaCuspFirstAtomScaledEvenJet k.val x =
      HTGeometry.firstAtomEvenTailProfile k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  fin_cases k
  · have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
    have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
    simp [thetaCuspFirstAtomScaledEvenJet, thetaCuspFirstAtomReflectionJet,
      HTGeometry.firstAtomEvenTailProfile]
    field_simp [hf]
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_1_eq_profile hq
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_2_eq_profile hq
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_3_eq_profile hq
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_4_eq_profile hq
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_5_eq_profile hq
  · exact thetaCuspFirstAtomScaledEvenJet_six_eq_profile hq

/-- Balanced complete moments reserve one hundred million in the last Gaussian coordinate. -/
def thetaCuspNativeEvenTailBalanced (k : Fin 7) (x : ℝ) : ℝ :=
  thetaCuspNativeScaledEvenJet k.val x/(32 : ℝ)^k.val -
    if k.val = 6 then 100000000/(32 : ℝ)^(6 : ℕ) else 0

/-- Balancing preserves the complete-source accuracy of every entry. -/
theorem abs_thetaCuspNativeEvenTailBalanced_sub_first_le {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
    |thetaCuspNativeEvenTailBalanced k x-
      HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)| ≤
        1/(10 : ℝ)^(10 : ℕ) := by
  have he := abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten_six (by omega : k.val ≤ 6) hq
  have hp : (1 : ℝ) ≤ 32^k.val := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 32) (Nat.zero_le k.val)
    simpa only [pow_zero] using h
  unfold thetaCuspNativeEvenTailBalanced HTGeometry.firstAtomEvenTailBalanced
  rw [← thetaCuspFirstAtomScaledEvenJet_fin_eq_profile hq k]
  rw [show thetaCuspNativeScaledEvenJet k.val x/(32 : ℝ)^k.val-
      (if k.val = 6 then 100000000/(32 : ℝ)^(6 : ℕ) else 0)-
      (thetaCuspFirstAtomScaledEvenJet k.val x/(32 : ℝ)^k.val-
        (if k.val = 6 then 100000000/(32 : ℝ)^(6 : ℕ) else 0)) =
      (thetaCuspNativeScaledEvenJet k.val x-thetaCuspFirstAtomScaledEvenJet k.val x)/(32 : ℝ)^k.val by ring]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 32^k.val)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32^k.val)).mpr
  nlinarith only [he, hp]

/-- The reserved complete-source determinant in fixed balanced coordinates. -/
def thetaCuspNativeEvenTailBalancedDet (x : ℝ) : ℝ :=
  hankelFourDet (thetaCuspNativeEvenTailBalanced 0 x) (thetaCuspNativeEvenTailBalanced 1 x)
    (thetaCuspNativeEvenTailBalanced 2 x) (thetaCuspNativeEvenTailBalanced 3 x)
    (thetaCuspNativeEvenTailBalanced 4 x) (thetaCuspNativeEvenTailBalanced 5 x)
    (thetaCuspNativeEvenTailBalanced 6 x)

/-- The entire infinite-source perturbation costs less than half the exact matrix reserve. -/
theorem thetaCuspNativeEvenTailBalancedDet_lower {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (1/20000 : ℝ) ≤ thetaCuspNativeEvenTailBalancedDet x := by
  have hu := inverseScale_bounds_of_thirty_le hq
  have hb (k : Fin 7) := HTGeometry.firstAtomEvenTailBalanced_abs_le hu.1 hu.2 k
  have he (k : Fin 7) := abs_thetaCuspNativeEvenTailBalanced_sub_first_le hq k
  have ha (k : Fin 7) : |thetaCuspNativeEvenTailBalanced k x| ≤ 5 := by
    have ht := abs_add_le
      (thetaCuspNativeEvenTailBalanced k x-
        HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      (HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
    rw [sub_add_cancel] at ht
    linarith [hb k, he k]
  have herr := hankelFourDet_error_le (M := 5) (δ := 1/(10 : ℝ)^(10 : ℕ))
    (by norm_num) (by positivity) ha (fun k => (hb k).trans (by norm_num : (4 : ℝ) ≤ 5)) he
  have hd := HTGeometry.firstAtomEvenTailBalancedDet_lower hu.1 hu.2
  change |thetaCuspNativeEvenTailBalancedDet x-
    HTGeometry.firstAtomEvenTailBalancedDet ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)| ≤ _ at herr
  have hl := (abs_le.mp herr).1
  linarith only [hl, hd]

end
end RHTower
