import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleLikelihoodBounds

/-!
# Positive lower-middle compensation and a sharp uniform middle loss bound

The complete likelihood first moment controls the full source slope. On scale
[37/10,5] the compensation is positive. Up to scale seven its adverse part is
at most one 2500th in the native determinant normalization.
-/
namespace RHTower
noncomputable section

private theorem first_slope_eq (x : ℝ) :
    deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)*
        (-8*thetaCuspSingleAtomReflectionScale 1 x^(3 : ℕ)+
          30*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-15*thetaCuspSingleAtomReflectionScale 1 x) := by
  have h := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
  rw [iteratedDeriv_one] at h
  rw [h]
  dsimp [thetaCuspGaussianScaleJet, thetaCuspGaussianScaleMoment]
  ring

private theorem first_slope_affine_lower {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (9/2-2*thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspSourceTerm x 1 ≤
      deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 ≤ q := by dsimp [q]; linarith
  rw [first_slope_eq, thetaCuspSourceTerm_one_eq_scale_profile]
  change (9/2-2*q)*(Real.exp (x/2-q)*(4*q^(2 : ℕ)-6*q)) ≤
    Real.exp (x/2-q)*(-8*q^(3 : ℕ)+30*q^(2 : ℕ)-15*q)
  nlinarith only [mul_nonneg (Real.exp_pos (x/2-q)).le hqp]

private theorem first_slope_lower_five {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    -(19/4)*thetaCuspSourceTerm x 1 ≤ deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 ≤ q := by dsimp [q]; linarith
  have hr : 0 ≤ (5-q)*(8*q-9)+3/2 := by
    have h1 : 0 ≤ 5-q := by dsimp [q]; linarith
    have h2 : 0 ≤ 8*q-9 := by dsimp [q]; linarith
    positivity
  have hp : 0 ≤ q*((5-q)*(8*q-9)+3/2) := mul_nonneg hqp hr
  have hm := mul_nonneg (Real.exp_pos (x/2-q)).le hp
  rw [first_slope_eq, thetaCuspSourceTerm_one_eq_scale_profile]
  change -(19/4)*(Real.exp (x/2-q)*(4*q^(2 : ℕ)-6*q)) ≤
    Real.exp (x/2-q)*(-8*q^(3 : ℕ)+30*q^(2 : ℕ)-15*q)
  nlinarith only [hm]

private theorem full_slope_transport {L x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hfL : L*thetaCuspSourceTerm x 1 ≤ deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x) :
    (L-thetaCuspSingleAtomReflectionScale 1 x/250)*thetaCuspFullSource x ≤
      deriv thetaCuspFullSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let R := thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 0
  let M := thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 1
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hR : 0 ≤ R := thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hM : M ≤ 1/500 := thetaCuspHigherLikelihoodSpectralMoment_one_le_middle hq
  have hF : f ≤ F := (thetaCuspFullSource_mass_bounds_middle hq).1
  have heF : F = f*(1+R) := by
    dsimp [F, f, R]
    rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hB,
      thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
  have hcore : L*F ≤ deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x*(1+R) := by
    rw [heF]
    nlinarith only [mul_le_mul_of_nonneg_right hfL (show 0 ≤ 1+R by linarith)]
  have htail := mul_le_mul_of_nonneg_left hM (show 0 ≤ 2*q*f by positivity)
  have hmass := mul_le_mul_of_nonneg_left hF (show 0 ≤ q/250 by positivity)
  have hd : deriv thetaCuspFullSource x =
      deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x*(1+R)-2*q*f*M :=
    deriv_thetaCuspFullSource_eq_likelihood_moment hx
  change (L-q/250)*F ≤ deriv thetaCuspFullSource x
  linarith only [hcore, htail, hmass, hd]

/-- The complete source logarithmic slope stays above minus five on the lower middle interval. -/
theorem thetaCuspFullSource_slope_lower_on_scale_five {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    -5*thetaCuspFullSource x ≤ deriv thetaCuspFullSource x := by
  have ht := full_slope_transport hq (first_slope_lower_five hq hqu)
  have hf := thetaCuspFullSource_pos_all x
  have hc : -(5 : ℝ) ≤ -(19/4)-thetaCuspSingleAtomReflectionScale 1 x/250 := by linarith
  exact (mul_le_mul_of_nonneg_right hc hf.le).trans ht

/-- Up to scale seven, the full source keeps the first atom's leading slope with a fixed reserve. -/
theorem thetaCuspFullSource_slope_affine_lower_middle {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    (4-2*thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspFullSource x ≤
      deriv thetaCuspFullSource x := by
  have ht := full_slope_transport hq (first_slope_affine_lower hq)
  have hf := thetaCuspFullSource_pos_all x
  have hc : 4-2*thetaCuspSingleAtomReflectionScale 1 x ≤
      9/2-2*thetaCuspSingleAtomReflectionScale 1 x-thetaCuspSingleAtomReflectionScale 1 x/250 := by linarith
  exact (mul_le_mul_of_nonneg_right hc hf.le).trans ht

/-- Scale at most five places the reflection center below one quarter. -/
theorem center_le_quarter_of_firstAtomScale_le_five {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) : x ≤ 1/4 := by
  by_contra hx
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) 3
  norm_num [Finset.sum_range_succ] at he
  have hp := mul_le_mul_of_nonneg_left
    (he.trans (Real.exp_le_exp.mpr (show (1/2 : ℝ) ≤ 2*x by linarith))) Real.pi_pos.le
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one] at hq
  nlinarith [Real.pi_gt_d2]

/-- Compensation is uniformly positive across the lower part of the remaining source gap. -/
theorem thetaCuspCenterCompensationSource_lower_on_scale_five {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    thetaCuspFullSource x^(2 : ℕ)/2 ≤ thetaCuspCenterCompensationSource x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hxu := center_le_quarter_of_firstAtomScale_le_five hqu
  have hF := thetaCuspFullSource_pos_all x
  have hs := mul_le_mul_of_nonneg_left (thetaCuspFullSource_slope_lower_on_scale_five hq hqu)
    (show 0 ≤ 2*x*thetaCuspFullSource x by positivity)
  have hr := mul_nonneg (show 0 ≤ 1/4-x by linarith) (sq_nonneg (thetaCuspFullSource x))
  unfold thetaCuspCenterCompensationSource
  nlinarith only [hs, hr]

/-- Positive compensation throughout the lower middle scale interval. -/
theorem thetaCuspCenterCompensationSource_pos_on_scale_five {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    0 < thetaCuspCenterCompensationSource x := by
  have hF := thetaCuspFullSource_pos_all x
  exact (by positivity : 0 < thetaCuspFullSource x^(2 : ℕ)/2).trans_le
    (thetaCuspCenterCompensationSource_lower_on_scale_five hq hqu)

/-- The complete compensation costs at most one 2500th in the Hankel normalization up to scale seven. -/
theorem thetaCuspCenterCompensationSource_middle_normalized_lower {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    -(1 : ℝ)/2500 ≤ thetaCuspCenterCompensationSource x/
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(5 : ℕ)) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let G := thetaCuspCenterCompensationSource x
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hs := mul_le_mul_of_nonneg_left (thetaCuspFullSource_slope_affine_lower_middle hq hqu)
    (show 0 ≤ 2*x*F by positivity)
  have hcoef : 0 ≤ 2*q-4 := by dsimp [q]; linarith
  have hc := mul_le_mul_of_nonneg_right (sixteen_mul_center_le_firstAtomScale hx.le)
    (mul_nonneg hcoef (sq_nonneg F))
  have hg : (3+q/2-q^(2 : ℕ)/4)*F^(2 : ℕ) ≤ G := by
    change (3+q/2-q^(2 : ℕ)/4)*F^(2 : ℕ) ≤ 3*F^(2 : ℕ)+2*x*F*deriv thetaCuspFullSource x
    change 2*x*F*((4-2*q)*F) ≤ 2*x*F*deriv thetaCuspFullSource x at hs
    change 16*x*((2*q-4)*F^(2 : ℕ)) ≤ q*((2*q-4)*F^(2 : ℕ)) at hc
    nlinarith only [hs, hc]
  have hpoly : -(q^(5 : ℕ)/2592) ≤ 3+q/2-q^(2 : ℕ)/4 := by
    have hp : 0 ≤ (q-6)^(2 : ℕ)*(q^(3 : ℕ)+12*q^(2 : ℕ)+108*q+216) := by positivity
    nlinarith only [hp]
  have hlow := (mul_le_mul_of_nonneg_right hpoly (sq_nonneg F)).trans hg
  have hm : F ≤ (101/100)*f := (thetaCuspFullSource_mass_bounds_middle hq).2
  have hm2 := pow_le_pow_left₀ hF.le hm 2
  have hneg := mul_le_mul_of_nonneg_left hm2 (show 0 ≤ q^(5 : ℕ)/2592 by positivity)
  have hraw : -(1 : ℝ)/2500*(f^(2 : ℕ)*q^(5 : ℕ)) ≤ G := by
    nlinarith only [hlow, hneg, mul_nonneg (sq_nonneg f) (pow_nonneg hq0.le 5)]
  change -(1 : ℝ)/2500 ≤ G/(f^(2 : ℕ)*q^(5 : ℕ))
  exact (le_div_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(5 : ℕ))).mpr hraw

end
end RHTower
