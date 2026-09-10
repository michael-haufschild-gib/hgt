import GaloisForLFunctions.RHTower.ThetaCuspModularBarrierCost
import GaloisForLFunctions.RHTower.ThetaCuspMiddleLikelihoodBounds

/-!
# A gap-scaled gain for the complete modular barrier flux

The full likelihood decomposition bounds the source slope above by the first
atom's slope. The modular source identity bounds it below by `-6*k*Phi`.
Together they give a physical-scale lower bound on `k`, and in particular
`k ≥ 3` on the ray `x ≥ 2/3`.

The signed polynomial flux estimate then supplies the positive reserve
`(5/48)*amp^2*T`. This exceeds fifteen times the earlier barrier reserve on
that whole ray. Global coefficient compatibility with the inner determinant
margin remains a separate sign problem.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.ThetaCuspModularRatio
noncomputable section

private theorem first_slope_eq (x : ℝ) :
    deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)*
        (-8*thetaCuspSingleAtomReflectionScale 1 x^3+
          30*thetaCuspSingleAtomReflectionScale 1 x^2-15*thetaCuspSingleAtomReflectionScale 1 x) := by
  have h := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
  rw [iteratedDeriv_one] at h
  rw [h]
  dsimp [thetaCuspGaussianScaleJet, thetaCuspGaussianScaleMoment]
  ring

private theorem full_slope_upper {x : ℝ}
    (hq : 15/2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    deriv thetaCuspFullSource x ≤ (5-2*thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspFullSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let R := thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 0
  let M := thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 1
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith only [hq])
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hq0 : 0 ≤ q := by dsimp [q]; linarith only [hq]
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hR : 0 ≤ R := thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hM : 0 ≤ M := thetaCuspHigherLikelihoodSpectralMoment_nonneg 1
  have heF : thetaCuspFullSource x = f*(1+R) := by
    dsimp [f, R]
    rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hB,
      thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
  have hfirst : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x ≤ (5-2*q)*f := by
    have hp := mul_nonneg hq0 (show 0 ≤ 2*q-15 by dsimp [q]; linarith only [hq])
    have hm := mul_nonneg (Real.exp_pos (x/2-q)).le hp
    rw [first_slope_eq]
    dsimp [f]
    rw [thetaCuspSourceTerm_one_eq_scale_profile]
    change Real.exp (x/2-q)*(-8*q^3+30*q^2-15*q) ≤
      (5-2*q)*(Real.exp (x/2-q)*(4*q^2-6*q))
    nlinarith only [hm]
  have hm := mul_le_mul_of_nonneg_right hfirst (show 0 ≤ 1+R by linarith only [hR])
  have htail : 0 ≤ 2*q*f*M := by positivity
  rw [deriv_thetaCuspFullSource_eq_likelihood_moment hx, heF]
  change deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x*(1+R)-2*q*f*M ≤ (5-2*q)*(f*(1+R))
  nlinarith only [hm, htail]

private theorem full_slope_ratio_lower {x : ℝ} (hx : 0 ≤ x) :
    -6*k x*thetaCuspFullSource x ≤ deriv thetaCuspFullSource x := by
  have hu := thetaCuspModularMassDrift_nonneg hx
  have hu3 := thetaCuspModularMassDrift_lt_three hx
  have hk := k_gt_fiveFourths hx
  have hj := J_nonneg hx
  have hgap : 0 ≤ 3-u x := sub_nonneg.mpr hu3.le
  have hv : 0 ≤ k x-1/6 := by linarith only [hk]
  have h1 : 0 ≤ (k x-1/6)*(u x/6+2*k x*(3-u x)) := by positivity
  have h2 : 0 ≤ 2*(k x+1/3)*J x := by positivity
  have hp : -6*k x*(k x-1/6) ≤ sourceFirstPolynomial x (J x) := by
    dsimp [sourceFirstPolynomial]
    nlinarith only [h1, h2]
  have ha : 0 ≤ sourceAmplitude x := by
    dsimp [sourceAmplitude]
    have ht := t_pos hx
    have hH := thetaCuspCompletedThetaProfile_pos x
    positivity
  have hm := mul_le_mul_of_nonneg_left hp ha
  rw [source_eq_ratio_coordinates hx, source_deriv_eq_ratio_coordinates hx]
  nlinarith only [hm]

/-- The physical first-atom scale gives a lower bound on the complete modular ratio. -/
theorem ratio_ge_physical_scale {x : ℝ}
    (hq : 15/2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x/3-5/6 ≤ k x := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith only [hq])
  have hl := full_slope_ratio_lower hx.le
  have hu := full_slope_upper hq
  have hp := thetaCuspFullSource_pos_all x
  have he : -6*k x ≤ 5-2*thetaCuspSingleAtomReflectionScale 1 x :=
    le_of_mul_le_mul_right (hl.trans hu) hp
  linarith only [he]

private theorem physical_scale_lower {x : ℝ} (hx : 2/3 ≤ x) :
    23/2 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4/3) 5
  norm_num [Finset.sum_range_succ] at he
  have hm := Real.exp_le_exp.mpr (show (4/3 : ℝ) ≤ 2*x by linarith only [hx])
  have hpi := Real.pi_gt_d2
  have hmul := mul_le_mul_of_nonneg_left (he.trans hm) Real.pi_pos.le
  norm_num [thetaCuspSingleAtomReflectionScale]
  nlinarith only [hpi, hmul]

/-- A source-fed ratio floor holds throughout the previously repaired upper ray. -/
theorem ratio_ge_three_on_upper_ray {x : ℝ} (hx : 2/3 ≤ x) : 3 ≤ k x := by
  have hq := physical_scale_lower hx
  have hk := ratio_ge_physical_scale (x := x) (by linarith only [hq])
  linarith only [hq, hk]

/-- The actual zero-integral flux supplies a gap-scaled reserve on the complete upper ray. -/
theorem barrierFlux_deriv_gap_gain {a x : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hx : 2/3 ≤ x) :
    (5/48 : ℝ)*(4*x*Real.sinh (2*a*x))*sourceAmplitude x^2*(t x*(k x+1/3)) ≤
      -deriv (barrierFlux a) x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hd := barrierFlux_deriv_polynomial_cost ha0 ha hx0
  have hk := ratio_ge_three_on_upper_ray hx
  have hu := thetaCuspModularMassDrift_lt_three hx0
  have hj := J_nonneg hx0
  have hm := mul_le_mul_of_nonneg_right hu.le (show 0 ≤ k x-2/3 by linarith only [hk])
  have hp : (6-3*k x+(u x*(k x-2/3)-J x)/4)/12 ≤ -(5/48 : ℝ) := by
    linarith only [hm, hj, hk]
  have hs := Real.sinh_nonneg_iff.mpr (show 0 ≤ 2*a*x by positivity)
  have ht := t_pos hx0
  have hf := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 4*x*Real.sinh (2*a*x)*sourceAmplitude x^2*(t x*(k x+1/3)) by positivity)
  nlinarith only [hd, hf]

/-- Gap-scaled source reserve obtained from the signed flux estimate. -/
def barrierGapReserve (x : ℝ) : ℝ := (5/48 : ℝ)*sourceAmplitude x^2*(t x*(k x+1/3))

/-- The gap-scaled reserve exceeds fifteen times the earlier upper-ray reserve. -/
theorem barrierGapReserve_ge_fifteen {x : ℝ} (hx : 2/3 ≤ x) :
    15*barrierReserve x ≤ barrierGapReserve x := by
  have hx0 : 0 < x := by linarith only [hx]
  have ht := t_pos hx0.le
  have hk := k_gt hx0.le
  have hT : 0 ≤ t x*(k x+1/3) := by positivity
  have hb := (barrierDefect_lt_gap hx0.le).le
  have hh := mul_le_mul_of_nonneg_left hx hT
  have hB : barrierDefect x ≤ t x*(k x+1/3)*x/8 := by
    nlinarith only [hb, hh]
  have hm := mul_le_mul_of_nonneg_left hB (sq_nonneg (sourceAmplitude x))
  dsimp [barrierReserve, barrierMass, barrierGapReserve]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (show 0 < 18*x by positivity)).mpr
  nlinarith only [hm]


end
end RHTower.ThetaCuspModularRatio
