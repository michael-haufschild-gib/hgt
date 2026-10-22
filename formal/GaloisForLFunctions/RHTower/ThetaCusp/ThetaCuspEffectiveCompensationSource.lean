import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveTailScale

/-! # Effective lower bound for the exact center-compensation source -/
namespace RHTower
noncomputable section

/-- The physical source scale dominates six times every real center. -/
theorem six_mul_center_le_firstAtomScale (x : ℝ) :
    6*x ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have he := Real.add_one_le_exp (2*x)
  have hp := Real.pi_gt_three
  have hm := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 3)
  have hm' := mul_le_mul_of_nonneg_right hp.le (Real.exp_pos (2*x)).le
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
  linarith

/-- A sharp enough first-atom slope bound retains the leading coefficient two. -/
theorem abs_deriv_firstAtom_le_two_scale {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤
      2*thetaCuspSingleAtomReflectionScale 1 x*thetaCuspSourceTerm x 1 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let e := Real.exp (x/2-q)
  have hqp : 0 ≤ q := by dsimp [q]; linarith
  have hq2 : 30*q ≤ q^(2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hq hqp
    change 30*q ≤ q*q at h
    nlinarith only [h]
  have hq3 : 30*q^(2 : ℕ) ≤ q^(3 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hq (sq_nonneg q)
    change 30*q^(2 : ℕ) ≤ q*q^(2 : ℕ) at h
    nlinarith only [h]
  have he : 0 < e := Real.exp_pos _
  have hd : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      e*(-8*q^(3 : ℕ)+30*q^(2 : ℕ)-15*q) := by
    have h := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
    rw [iteratedDeriv_one] at h
    rw [h]
    dsimp [thetaCuspGaussianScaleJet, thetaCuspGaussianScaleMoment, e, q]
    ring
  have hpoly : |-8*q^(3 : ℕ)+30*q^(2 : ℕ)-15*q| ≤ 2*q*(4*q^(2 : ℕ)-6*q) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hq2, hq3, hqp]
  rw [hd, abs_mul, abs_of_pos he, thetaCuspSourceTerm_one_eq_scale_profile]
  change e*|-8*q^(3 : ℕ)+30*q^(2 : ℕ)-15*q| ≤ 2*q*(e*(4*q^(2 : ℕ)-6*q))
  have hm := mul_le_mul_of_nonneg_left hpoly he.le
  nlinarith only [hm]

/-- Complete-source mass and slope have concrete first-atom majorants on the scale-thirty ray. -/
theorem thetaCuspFullSource_mass_slope_le_effective {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFullSource x ≤ 2*thetaCuspSourceTerm x 1 ∧
    |deriv thetaCuspFullSource x| ≤
      3*thetaCuspSingleAtomReflectionScale 1 x*thetaCuspSourceTerm x 1 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let ε := regimeOneLikelihoodScale x
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < q := by dsimp [q]; linarith
  have he := regimeOneLikelihoodScale_le_of_six_le (x := x) (by linarith)
  have h0 := abs_thetaCuspFullSource_derivative_sub_first_le_effective 0 hx (by norm_num; linarith)
  have h1 := abs_thetaCuspFullSource_derivative_sub_first_le_effective 1 hx (by norm_num; linarith)
  simp only [iteratedDeriv_zero, pow_zero, mul_one] at h0
  simp only [iteratedDeriv_one, pow_one] at h1
  have hs := abs_deriv_firstAtom_le_two_scale hq
  constructor
  · have hb := (abs_le.mp h0).2
    have hm := mul_le_mul_of_nonneg_right (show 3*ε ≤ 1 by dsimp [ε]; linarith) hf.le
    change 3*ε*f ≤ 1*f at hm
    change thetaCuspFullSource x ≤ 2*f
    change thetaCuspFullSource x-f ≤ 3*ε*f at hb
    nlinarith only [hm, hb]
  · have ht := abs_add_le
      (deriv thetaCuspFullSource x-deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x)
      (deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x)
    rw [sub_add_cancel] at ht
    have hm := mul_le_mul_of_nonneg_right (show 36*ε ≤ 1 by dsimp [ε]; linarith)
      (mul_nonneg hqp.le hf.le)
    change 36*ε*(q*f) ≤ 1*(q*f) at hm
    change |deriv thetaCuspFullSource x-deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤
      3*(12*q)*ε*f at h1
    change |deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤ 2*q*f at hs
    change |deriv thetaCuspFullSource x| ≤ 3*q*f
    nlinarith only [ht, h1, hs, hm]

/-- The potentially negative compensation source has a uniform normalized lower bound. -/
theorem thetaCuspCenterCompensationSource_normalized_lower {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -(2 : ℝ)/30^(3 : ℕ) ≤ thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^(2 : ℕ) * thetaCuspSingleAtomReflectionScale 1 x^(5 : ℕ)) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let d := deriv thetaCuspFullSource x
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hb := thetaCuspFullSource_mass_slope_le_effective hq
  change F ≤ 2*f ∧ |d| ≤ 3*q*f at hb
  have hprod := mul_le_mul hb.1 hb.2 (abs_nonneg d) (by positivity : (0 : ℝ) ≤ 2*f)
  have hprod' := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2*x)
  have hxd := six_mul_center_le_firstAtomScale x
  change 6*x ≤ q at hxd
  have hscale := mul_le_mul_of_nonneg_right hxd (by positivity : (0 : ℝ) ≤ 2*q*f^(2 : ℕ))
  have hd := (abs_le.mp (le_refl |d|)).1
  have hneg := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2*x*F)
  have hraw : -2*q^(2 : ℕ)*f^(2 : ℕ) ≤ thetaCuspCenterCompensationSource x := by
    change -2*q^(2 : ℕ)*f^(2 : ℕ) ≤ 3*F^(2 : ℕ)+2*x*F*d
    nlinarith only [hprod', hscale, hneg, sq_nonneg F]
  have hp3 : (30 : ℝ)^(3 : ℕ) ≤ q^(3 : ℕ) := pow_le_pow_left₀ (by norm_num) hq 3
  have hnorm : -(2 : ℝ)/q^(3 : ℕ) ≤ thetaCuspCenterCompensationSource x/(f^(2 : ℕ)*q^(5 : ℕ)) := by
    apply (le_div_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(5 : ℕ))).mpr
    calc
      (-(2 : ℝ)/q^(3 : ℕ))*(f^(2 : ℕ)*q^(5 : ℕ)) = -2*q^(2 : ℕ)*f^(2 : ℕ) := by field_simp
      _ ≤ thetaCuspCenterCompensationSource x := hraw
  have hi : (1 : ℝ)/q^(3 : ℕ) ≤ 1/(30 : ℝ)^(3 : ℕ) :=
    one_div_le_one_div_of_le (by norm_num) hp3
  change -(2 : ℝ)/30^(3 : ℕ) ≤ thetaCuspCenterCompensationSource x/(f^(2 : ℕ)*q^(5 : ℕ))
  simp only [div_eq_mul_inv] at hi hnorm ⊢
  linarith only [hi, hnorm]

end
end RHTower
