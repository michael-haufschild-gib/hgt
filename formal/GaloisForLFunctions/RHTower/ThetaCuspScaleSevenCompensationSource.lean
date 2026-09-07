import GaloisForLFunctions.RHTower.ThetaCuspScaleSevenLikelihood
import GaloisForLFunctions.RHTower.ThetaCuspEffectiveCompensationSource

/-! # Sharper compensation-source bounds for the scale-seven determinant reserve -/
namespace RHTower
noncomputable section

/-- A uniform exponential bound controls the entire nonnegative center by one sixteenth of scale. -/
theorem sixteen_mul_center_le_firstAtomScale {x : ℝ} (hx : 0 ≤ x) :
    16*x ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have he1 : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := mul_le_mul Real.pi_gt_three.le he1 (by norm_num : (0 : ℝ) ≤ 27/10) Real.pi_pos.le
  have h8 : (8 : ℝ) ≤ Real.pi*Real.exp 1 := by nlinarith only [hp]
  have hm := mul_le_mul_of_nonneg_right h8 hx
  have he := Real.add_one_le_exp (2*x-1)
  have he' := mul_le_mul_of_nonneg_left he
    (mul_nonneg Real.pi_pos.le (Real.exp_pos 1).le)
  simp only [mul_assoc] at he'
  rw [← Real.exp_add, show 1+(2*x-1) = 2*x by ring] at he'
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
  nlinarith only [hm, he']

/-- A sharp enough first-atom slope bound retains the leading coefficient two. -/
theorem abs_deriv_firstAtom_le_two_scale_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤
      2*thetaCuspSingleAtomReflectionScale 1 x*thetaCuspSourceTerm x 1 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let e := Real.exp (x/2-q)
  have hqp : 0 ≤ q := by dsimp [q]; linarith
  have hq2 : 7*q ≤ q^2 := by
    have h := mul_le_mul_of_nonneg_right hq hqp
    change 7*q ≤ q*q at h
    nlinarith only [h]
  have hq3 : 7*q^2 ≤ q^3 := by
    have h := mul_le_mul_of_nonneg_right hq (sq_nonneg q)
    change 7*q^2 ≤ q*q^2 at h
    nlinarith only [h]
  have he : 0 < e := Real.exp_pos _
  have hd : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      e*(-8*q^3+30*q^2-15*q) := by
    have h := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
    rw [iteratedDeriv_one] at h
    rw [h]
    dsimp [thetaCuspGaussianScaleJet, thetaCuspGaussianScaleMoment, e, q]
    ring
  have hpoly : |-8*q^3+30*q^2-15*q| ≤ 2*q*(4*q^2-6*q) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hq2, hq3, hqp]
  rw [hd, abs_mul, abs_of_pos he, thetaCuspSourceTerm_one_eq_scale_profile]
  change e*|-8*q^3+30*q^2-15*q| ≤ 2*q*(e*(4*q^2-6*q))
  have hm := mul_le_mul_of_nonneg_left hpoly he.le
  nlinarith only [hm]

/-- The complete source mass and slope stay within small fixed enlargements of the leading atom. -/
theorem thetaCuspFullSource_mass_slope_le_scaleSeven {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFullSource x ≤ (101/100)*thetaCuspSourceTerm x 1 ∧
    |deriv thetaCuspFullSource x| ≤
      (201/100)*thetaCuspSingleAtomReflectionScale 1 x*thetaCuspSourceTerm x 1 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let ε := regimeOneLikelihoodScale x
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < q := by dsimp [q]; linarith
  have he := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by norm_num) hq
  simp only [pow_zero, one_mul] at he
  have h0 := abs_thetaCuspFullSource_derivative_sub_first_le_effective 0 hx (by norm_num; linarith)
  have h1 := abs_thetaCuspFullSource_derivative_sub_first_le_effective 1 hx (by norm_num; linarith)
  simp only [iteratedDeriv_zero, pow_zero, mul_one] at h0
  simp only [iteratedDeriv_one, pow_one] at h1
  have hs := abs_deriv_firstAtom_le_two_scale_of_seven_le hq
  constructor
  · have hb := (abs_le.mp h0).2
    have hm := mul_le_mul_of_nonneg_right (show 3*ε ≤ 1/100 by dsimp [ε]; linarith) hf.le
    change 3*ε*f ≤ (1/100)*f at hm
    change thetaCuspFullSource x ≤ (101/100)*f
    change thetaCuspFullSource x-f ≤ 3*ε*f at hb
    nlinarith only [hm, hb]
  · have ht := abs_add_le
      (deriv thetaCuspFullSource x-deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x)
      (deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x)
    rw [sub_add_cancel] at ht
    have hm := mul_le_mul_of_nonneg_right (show 36*ε ≤ 1/100 by dsimp [ε]; linarith)
      (mul_nonneg hqp.le hf.le)
    change 36*ε*(q*f) ≤ (1/100)*(q*f) at hm
    change |deriv thetaCuspFullSource x-deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤
      3*(12*q)*ε*f at h1
    change |deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤ 2*q*f at hs
    change |deriv thetaCuspFullSource x| ≤ (201/100)*q*f
    nlinarith only [ht, h1, hs, hm]

/-- The normalized adverse compensation is bounded uniformly on the entire scale-seven ray. -/
theorem thetaCuspCenterCompensationSource_scaleSeven_normalized_lower {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -(13/50 : ℝ)/7^3 ≤ thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^5) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let d := deriv thetaCuspFullSource x
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hb := thetaCuspFullSource_mass_slope_le_scaleSeven hq
  change F ≤ (101/100)*f ∧ |d| ≤ (201/100)*q*f at hb
  have hprod := mul_le_mul hb.1 hb.2 (abs_nonneg d) (by positivity : (0 : ℝ) ≤ (101/100)*f)
  have hprod1 : F*|d| ≤ (52/25)*q*f^2 := by
    have hpos : 0 ≤ q*f^2 := by positivity
    nlinarith only [hprod, hpos]
  have hprod2 := mul_le_mul_of_nonneg_left hprod1 (by positivity : (0 : ℝ) ≤ 2*x)
  have hxd := sixteen_mul_center_le_firstAtomScale hx.le
  change 16*x ≤ q at hxd
  have hscale := mul_le_mul_of_nonneg_right hxd (by positivity : (0 : ℝ) ≤ (13/50)*q*f^2)
  have hd := neg_abs_le d
  have hneg := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2*x*F)
  have hraw : -(13/50)*q^2*f^2 ≤ thetaCuspCenterCompensationSource x := by
    change -(13/50)*q^2*f^2 ≤ 3*F^2+2*x*F*d
    nlinarith only [hprod2, hscale, hneg, sq_nonneg F]
  have hnorm : -(13/50 : ℝ)/q^3 ≤ thetaCuspCenterCompensationSource x/(f^2*q^5) := by
    apply (le_div_iff₀ (by positivity : 0 < f^2*q^5)).mpr
    calc
      (-(13/50 : ℝ)/q^3)*(f^2*q^5) = -(13/50)*q^2*f^2 := by field_simp
      _ ≤ thetaCuspCenterCompensationSource x := hraw
  have hp3 : (7 : ℝ)^3 ≤ q^3 := pow_le_pow_left₀ (by norm_num) hq 3
  have hi : (1 : ℝ)/q^3 ≤ 1/(7 : ℝ)^3 := one_div_le_one_div_of_le (by norm_num) hp3
  change -(13/50 : ℝ)/7^3 ≤ thetaCuspCenterCompensationSource x/(f^2*q^5)
  simp only [div_eq_mul_inv] at hi hnorm ⊢
  linarith only [hi, hnorm]

end
end RHTower
