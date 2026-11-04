import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleThirtyTwoData
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossLoad
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveTailScale

/-!
# Complete-source bounds at theta scale thirty-two

The all-order likelihood estimate controls every even moment through order
sixteen. Explicit center and slope bounds control the differentiated quartic
profile using the complete theta source.
-/

noncomputable section
open Matrix RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.ThirtyTwoCrossSource
open FifthNativeRay FifthLeadingPair FifthRemainder FifthCrossEnvelope

/-- The center at which the first reflected atom has scale thirty-two. -/
def center : ℝ := Real.log (32/Real.pi)/2

theorem center_scale : thetaCuspSingleAtomReflectionScale 1 center = 32 := by
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one,center]
  rw [show 2*(Real.log (32/Real.pi)/2)=Real.log (32/Real.pi) by ring,
    Real.exp_log (div_pos (by norm_num) Real.pi_pos)]
  field_simp [Real.pi_pos.ne']

theorem center_pos : 0 < center :=
  regimeOne_pos_of_six_le (by rw [center_scale]; norm_num)

private theorem lower_center_exponential : Real.pi*Real.exp (9/4) ≤ (32 : ℝ) := by
  have h1 : Real.exp 1 ≤ (11/4 : ℝ) := by linarith only [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le h1 9
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat,mul_one] at hp
  have hp4 : Real.exp (9/4 : ℝ)^4 ≤ (10 : ℝ)^4 := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat,show (4 : ℝ)*(9/4)=9 by norm_num]
    exact hp.trans (by norm_num)
  have he : Real.exp (9/4 : ℝ) ≤ 10 := by
    by_contra h
    have hh := pow_lt_pow_left₀ (lt_of_not_ge h) (by norm_num : (0 : ℝ) ≤ 10)
      (by norm_num : (4 : ℕ) ≠ 0)
    exact (not_lt_of_ge hp4) hh
  have hpi : Real.pi ≤ (22/7 : ℝ) := by linarith only [Real.pi_lt_d4]
  have hh := mul_le_mul hpi he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 22/7)
  linarith only [hh]

private theorem upper_center_exponential : (32 : ℝ) ≤ Real.pi*Real.exp (12/5) := by
  have h := Real.sum_le_exp_of_nonneg (x := (12/5 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have he : (32/3 : ℝ) ≤ Real.exp (12/5) := by linarith only [h]
  have hh := mul_le_mul (le_of_lt Real.pi_gt_three) he
    (by norm_num : (0 : ℝ) ≤ 32/3) Real.pi_pos.le
  linarith only [hh]

/-- Rational center bounds straddle the full first-atom scale exactly. -/
theorem center_bounds : (9/8 : ℝ) ≤ center ∧ center ≤ 6/5 := by
  have hs : Real.pi*Real.exp (2*center)=32 := by
    simpa only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one] using center_scale
  constructor
  · have he : Real.exp (9/4 : ℝ) ≤ Real.exp (2*center) := by
      by_contra h
      have hp := mul_pos Real.pi_pos (sub_pos.mpr (lt_of_not_ge h))
      nlinarith only [hp,lower_center_exponential,hs]
    have h := Real.exp_le_exp.mp he
    linarith only [h]
  · have he : Real.exp (2*center) ≤ Real.exp (12/5 : ℝ) := by
      by_contra h
      have hp := mul_pos Real.pi_pos (sub_pos.mpr (lt_of_not_ge h))
      nlinarith only [hp,upper_center_exponential,hs]
    have h := Real.exp_le_exp.mp he
    linarith only [h]

private theorem exp_neg_six_bound : Real.exp (-6 : ℝ) ≤ 1/400 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have h3 : (20 : ℝ) ≤ Real.exp 3 := by linarith only [h]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) h3 2
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat,show (2 : ℝ)*3=6 by norm_num] at hp
  rw [Real.exp_neg,inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 400) hp

private theorem base_scale_bound :
    Real.exp (3*Real.pi)/399*Real.exp (-(3*(32 : ℝ))) ≤ 8/(10 : ℝ)^41 := by
  have he : Real.exp (-(3*(32 : ℝ)))=Real.exp (-(3*30))*Real.exp (-6) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he,← mul_assoc]
  have h := mul_le_mul base_scale_thirty_le exp_neg_six_bound
    (Real.exp_pos _).le (by positivity : (0 : ℝ) ≤ 32/(10 : ℝ)^39)
  exact h.trans (by norm_num)

/-- All nine normalized even moments have a uniform complete-source error above scale thirty-two. -/
theorem scaled_even_error {k : ℕ} (hk : k ≤ 8) {x : ℝ}
    (hq : 32 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| ≤ 1/10000 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith only [hq]
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith only [hq])
  have hk16 : 2*k ≤ 16 := by omega
  have hkr : ((2*k : ℕ) : ℝ) ≤ 16 := by exact_mod_cast hk16
  have he := abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective k hx
    (by linarith only [hq,hkr])
  have hb := pow_mul_regimeOneLikelihoodScale_le (k := 8) (A₁ := 32)
    (by norm_num) (by norm_num) hq
  have htail := mul_le_mul_of_nonneg_left base_scale_bound (by positivity : (0 : ℝ) ≤ 32^8)
  have hq8 : q^8*regimeOneLikelihoodScale x ≤ (32 : ℝ)^8*(8/(10 : ℝ)^41) :=
    hb.trans htail
  have hp24 : (24 : ℝ)^(2*k) ≤ (24 : ℝ)^16 :=
    pow_le_pow_right₀ (by norm_num) hk16
  have hpq : q^k ≤ q^8 := pow_le_pow_right₀ (by dsimp only [q]; linarith only [hq]) hk
  have hprod := mul_le_mul hp24 hpq (pow_nonneg hq0 k) (by positivity)
  have hprod' := mul_le_mul_of_nonneg_right hprod (regimeOneLikelihoodScale_pos x).le
  have hlast := mul_le_mul_of_nonneg_left hq8 (by positivity : (0 : ℝ) ≤ 27*24^16)
  have hc : 27*(24 : ℝ)^16*(32^8*(8/(10 : ℝ)^41)) ≤ 1/10000 := by norm_num
  change |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| ≤
    27*(24 : ℝ)^(2*k)*q^k*regimeOneLikelihoodScale x at he
  nlinarith only [he,hprod',hlast,hc]

private theorem likelihood_bound : regimeOneLikelihoodScale center ≤ 8/(10 : ℝ)^41 := by
  have h := pow_mul_regimeOneLikelihoodScale_le (k := 0) (A₁ := 32)
    (by norm_num) (by norm_num) (by rw [center_scale])
  simp only [pow_zero,one_mul] at h
  exact h.trans base_scale_bound

/-- The complete source has a uniformly negative logarithmic slope at scale thirty-two. -/
theorem derivative_upper : deriv thetaCuspFullSource center ≤ -59*thetaCuspFullSource center := by
  have hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 center := by rw [center_scale]; norm_num
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos center_pos (by norm_num : 0 < (1 : ℕ))
  have hm := (mass_slope_bounds hq).2.1
  have he := abs_thetaCuspFullSource_derivative_sub_first_le_effective 1 center_pos
    (by rw [center_scale]; norm_num)
  simp only [iteratedDeriv_one,pow_one,first_derivative hq,center_scale] at he
  norm_num only [firstSlope] at he
  have hs : 36*32*regimeOneLikelihoodScale center ≤ (1/100000 : ℝ) := by
    linarith only [likelihood_bound]
  have hp := mul_le_mul_of_nonneg_right hs hf.le
  have hu := (abs_le.mp he).2
  nlinarith only [hp,hu,hm,hf.le]

private theorem base_compensation_upper :
    thetaCuspCenterCompensationSource center ≤ -(519/4)*thetaCuspFullSource center^2 := by
  have hF := (thetaCuspFullSource_pos_all center).le
  have hx := center_pos.le
  have hd := mul_le_mul_of_nonneg_left derivative_upper
    (show 0 ≤ 2*center*thetaCuspFullSource center by positivity)
  have hxl := mul_le_mul_of_nonneg_right center_bounds.1 (sq_nonneg (thetaCuspFullSource center))
  unfold thetaCuspCenterCompensationSource
  nlinarith only [hd,hxl]

/-- The quartic correction is strongly negative at scale thirty-two, including its derivative term. -/
theorem profile_compensation_upper :
    FifthPolynomialCross.compensation center ≤ -280*thetaCuspFullSource center^2 := by
  let t := 2*center^2-1
  have hxlo := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 9/8) center_bounds.1
  have hxhi := mul_self_le_mul_self center_pos.le center_bounds.2
  have htlo : (49/32 : ℝ) ≤ t := by dsimp only [t]; nlinarith only [hxlo]
  have hthi : t ≤ (47/25 : ℝ) := by dsimp only [t]; nlinarith only [hxhi]
  have ht : 0 ≤ t := by linarith only [htlo]
  have htsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 49/32) htlo
  have hG := mul_le_mul_of_nonneg_left base_compensation_upper (sq_nonneg t)
  have htp := mul_le_mul_of_nonneg_right htsq (sq_nonneg (thetaCuspFullSource center))
  have hx2 : center^2 ≤ (36/25 : ℝ) := by nlinarith only [hxhi]
  have hcoef := mul_le_mul hx2 hthi ht (by norm_num : (0 : ℝ) ≤ 36/25)
  have hpay := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (thetaCuspFullSource center))
  have he : FifthPolynomialCross.compensation center =
      t^2*thetaCuspCenterCompensationSource center+8*center^2*t*thetaCuspFullSource center^2 := by
    dsimp only [FifthPolynomialCross.compensation,t]
    ring
  rw [he]
  nlinarith only [hG,htp,hpay,sq_nonneg (thetaCuspFullSource center)]

/-- The same strict loss in the common first-pair normalization. -/
theorem normalized_compensation_upper :
    FifthPolynomialCross.compensation center/sourceUnit center ≤ -280*61^2 := by
  have hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 center := by rw [center_scale]; norm_num
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos center_pos (by norm_num : 0 < (1 : ℕ))
  have hm := mul_self_le_mul_self hf.le (mass_slope_bounds hq).1
  have hs := first_mass_square center
  rw [center_scale] at hs
  apply (div_le_iff₀ hK).mpr
  nlinarith only [profile_compensation_upper,hm,hs]

private theorem normalized_entry_difference (k : ℕ) :
    (-1 : ℝ)^k*thetaCuspNativeReflectionJet (2*k) center/
        (sourceUnit center*32^k)-leadingMoment 32 0 k =
      61^2*(thetaCuspNativeScaledEvenJet k center-thetaCuspFirstAtomScaledEvenJet k center) := by
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos center_pos (by norm_num : 0 < (1 : ℕ))
  have hs := first_mass_square center
  rw [center_scale] at hs
  norm_num only [show (2*(32 : ℝ)-3)^2=61^2 by norm_num] at hs
  have hj := _root_.RHTower.ThetaCuspOddFourThreeAtom.signed_pair_even 1 1 k center
  change (-1 : ℝ)^k*thetaCuspFirstAtomReflectionJet (2*k) center = _ at hj
  simp only [Nat.cast_one,one_pow,one_mul,mul_one,center_scale] at hj
  have hr : (-1 : ℝ)^k*thetaCuspFirstAtomReflectionJet (2*k) center =
      sourceUnit center*(thetaPairRadialEvenPolynomial (32^2) k).eval (2*32) := by
    simpa only [sourceUnit,center_scale,show (1 : ℝ)+1=2 by norm_num] using hj
  unfold thetaCuspNativeScaledEvenJet thetaCuspFirstAtomScaledEvenJet leadingMoment
  rw [center_scale,hs,hr]
  simp only [mul_zero,zero_mul,add_zero]
  field_simp [hK.ne']
  ring

/-- In the last Gaussian coordinate, the entire source differs from its first atom by less than one. -/
theorem source_last_error :
    |sourceGram center 4 4-gaussianGram (leadingMatrix 32 0) 4 4| ≤ 1 := by
  let A : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
    (-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) center/
      (sourceUnit center*32^(i.val+j.val))-leadingMoment 32 0 (i.val+j.val)
  have hA (i j : Fin 5) : |A i j| ≤ (61^2/10000 : ℝ) := by
    have h := scaled_even_error (k := i.val+j.val) (by omega)
      (x := center) (by rw [center_scale])
    have hp := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 61^2)
    dsimp only [A]
    rw [normalized_entry_difference,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 61^2)]
    linarith only [hp]
  have he : sourceGram center 4 4-gaussianGram (leadingMatrix 32 0) 4 4=gaussianGram A 4 4 := by
    simp only [sourceGram,normalizedGram,gaussianGram,nativeShiftedMatrix,add_zero,
      center_scale,leadingMatrix,A,mul_sub,Finset.sum_sub_distrib]
  rw [he]
  have h := gaussian_entry_majorant A (fun _ => (61^2/10000 : ℝ)) hA 4 4
  have hb : (∑ u : Fin 5, ∑ v : Fin 5,
      |gaussianBasis 4 u| * |gaussianBasis 4 v| * (61^2/10000 : ℝ)) ≤ 1 := by
    norm_num [gaussianBasis,Fin.sum_univ_succ]
  exact h.trans hb

private theorem exp_six_fifths_le_four : Real.exp (6/5 : ℝ) ≤ 4 := by
  have he : Real.exp 1 ≤ (11/4 : ℝ) := by linarith only [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he 6
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat,mul_one] at hp
  have h5 : Real.exp (6/5 : ℝ)^5 ≤ (4 : ℝ)^5 := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat,show (5 : ℝ)*(6/5)=6 by norm_num]
    exact hp.trans (by norm_num)
  by_contra h
  have hh := pow_lt_pow_left₀ (lt_of_not_ge h) (by norm_num : (0 : ℝ) ≤ 4)
    (by norm_num : (5 : ℕ) ≠ 0)
  exact (not_lt_of_ge h5) hh

private theorem hyperbolic_remainder_upper {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 6/5) :
    u*Real.cosh u-Real.sinh u ≤ 3*Real.sinh u := by
  have hc := (HTGeometry.cosh_le_exp_of_nonneg hu).trans
    ((Real.exp_le_exp.mpr hu1).trans exp_six_fifths_le_four)
  have hp := mul_le_mul_of_nonneg_left hc hu
  have hs := HTGeometry.self_le_sinh_of_nonneg hu
  linarith only [hp,hs]

/-- Every critical aperture retains the negative differentiated profile at this center. -/
theorem weighted_derivative_upper {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) :
    deriv (FifthPolynomialCross.flux a) (2*center) ≤
      (2*center*Real.sinh (a*(2*center)))*(-268*thetaCuspFullSource center^2) := by
  have hx := center_pos.le
  have hr : 0 ≤ 2*center := by positivity
  have hu : 0 ≤ a*(2*center) := mul_nonneg ha0 hr
  have hu1 : a*(2*center) ≤ 6/5 := by
    have h := mul_le_mul_of_nonneg_right ha.le hr
    linarith only [h,center_bounds.2]
  have hs : 0 ≤ Real.sinh (a*(2*center)) := Real.sinh_nonneg_iff.mpr hu
  have hx2 := mul_self_le_mul_self center_pos.le center_bounds.2
  have htlo : 0 ≤ 2*center^2-1 := by
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 9/8) center_bounds.1
    nlinarith only [h]
  have hthi : 2*center^2-1 ≤ (47/25 : ℝ) := by nlinarith only [hx2]
  have hp : FifthPolynomialCross.profile (2*center) ≤ 4 := by
    have h := mul_self_le_mul_self htlo hthi
    unfold FifthPolynomialCross.profile
    nlinarith only [h]
  have hrem := mul_le_mul_of_nonneg_left (hyperbolic_remainder_upper hu hu1)
    (show 0 ≤ FifthPolynomialCross.profile (2*center)*(2*center)*thetaCuspFullSource center^2 from
      mul_nonneg (mul_nonneg (FifthPolynomialCross.profile_nonneg _) hr) (sq_nonneg _))
  have hprof := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ (2*center)*Real.sinh (a*(2*center))*thetaCuspFullSource center^2 by positivity)
  have hmain := mul_le_mul_of_nonneg_left profile_compensation_upper (mul_nonneg hr hs)
  rw [FifthPolynomialCross.deriv_flux_remainder,show 2*center/2=center by ring]
  nlinarith only [hrem,hprof,hmain]

end GaloisForLFunctions.ThetaCuspSections.ThirtyTwoCrossSource
