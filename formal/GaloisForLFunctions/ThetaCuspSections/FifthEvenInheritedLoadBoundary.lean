import GaloisForLFunctions.RHTower.CothInfra
import GaloisForLFunctions.ThetaCuspSections.FifthEvenSourceRepair
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspScaleSevenCompensationSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterCompensationTransitionSlack
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedCauchyTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspInheritedOddCompensationBoundary

/-!
# Inherited load boundary for the fifth even theta source

An explicit even direction has positive complete-source energy at scale seven.
The fixed fourth-diagonal correction makes it negative, and every nonnegative
fifth load worsens it. This persists for every critical aperture in the actual
weighted flux representative. Exact positive capacities classify the two loads.
-/

noncomputable section
open Matrix RHTower Polynomial RHTower.ThetaCuspReflectedCauchyTail
open HTGeometry.SignedPoisson
namespace GaloisForLFunctions.ThetaCuspSections.EvenFiveBoundary

private theorem compensation_upper {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) (hx : 2/5 ≤ x) :
    thetaCuspCenterCompensationSource x ≤
      -(229/55 : ℝ)*thetaCuspSourceTerm x 1^2 := by
  have hx0 : 0 < x := by linarith
  let f := thetaCuspSourceTerm x 1
  let R := thetaCuspLikelihoodSourceRemainder x
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)
  have hF : 0 < thetaCuspFullSource x := thetaCuspFullSource_pos_all x
  have hR := (thetaCuspLikelihoodSourceRemainder_signed_bounds_of_seven_le
    (n := 0) (by norm_num) (x := x) (by rw [hq])).1
  have hD := (thetaCuspLikelihoodSourceRemainder_signed_bounds_of_seven_le
    (n := 1) (by norm_num) (x := x) (by rw [hq])).1
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at hR
  simp only [pow_one, neg_one_mul, iteratedDeriv_one] at hD
  have hzero := thetaCuspFullSource_derivative_sub_first_eq 0 hx0
  have hone := thetaCuspFullSource_derivative_sub_first_eq 1 hx0
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, Nat.reduceSub, one_mul, iteratedDeriv_zero,
    iteratedDeriv_one, add_zero, zero_add] at hzero hone
  have hslope : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x = -(197/22 : ℝ)*f := by
    have hd := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
    rw [iteratedDeriv_one] at hd
    rw [hd]
    dsimp only [thetaCuspGaussianScaleJet, thetaCuspGaussianScaleMoment, f]
    rw [thetaCuspSourceTerm_one_eq_scale_profile, hq]
    ring
  have hmass : f ≤ thetaCuspFullSource x := by
    have hp := mul_nonneg hf.le hR
    dsimp [f] at hp ⊢
    linarith only [hzero, hp]
  have hs : deriv thetaCuspFullSource x ≤ -(197/22 : ℝ)*thetaCuspFullSource x := by
    have hp : f*deriv thetaCuspLikelihoodSourceRemainder x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hf.le (by linarith only [hD])
    rw [hslope] at hone
    change thetaCuspFullSource x-f = f*R at hzero
    change deriv thetaCuspFullSource x-(-(197/22 : ℝ)*f) =
      f*deriv thetaCuspLikelihoodSourceRemainder x+(-(197/22 : ℝ)*f)*R at hone
    nlinarith only [hone, hzero, hp]
  have hprod := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2*x*thetaCuspFullSource x by positivity)
  have hxprod := mul_le_mul_of_nonneg_right hx (sq_nonneg (thetaCuspFullSource x))
  have hsq := mul_self_le_mul_self hf.le hmass
  unfold thetaCuspCenterCompensationSource
  change 3*thetaCuspFullSource x^2+2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x ≤
    -(229/55 : ℝ)*f^2
  nlinarith only [hprod, hxprod, hsq]

private theorem exp_three_lower : (20 : ℝ) ≤ Real.exp 3 := by
  have h1 : (2718/1000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) h1 3
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

private theorem second_decay_bound : Real.exp (-21 : ℝ) ≤ 1/1000000000 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) exp_three_lower 7
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hp])

/-- Positive center whose first Gaussian atom has scale seven. -/
noncomputable def witnessCenter : ℝ := Real.log (7/Real.pi)/2

private theorem witness_scale : thetaCuspSingleAtomReflectionScale 1 witnessCenter=7 := by
  unfold thetaCuspSingleAtomReflectionScale witnessCenter
  norm_num only [Nat.cast_one, one_pow, mul_one]
  rw [show (2:ℝ)*(Real.log (7/Real.pi)/2)=Real.log (7/Real.pi) by ring,
    Real.exp_log (by positivity)]
  field_simp

private theorem witness_center_lower : (2/5 : ℝ) ≤ witnessCenter := by
  have he1 : Real.exp 1 ≤ (2719/1000 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he4 := pow_le_pow_left₀ (Real.exp_pos 1).le he1 4
  rw [← Real.exp_nat_mul] at he4
  norm_num at he4
  have he5 : Real.exp (4/5 : ℝ)^5=Real.exp 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp (4/5 : ℝ) ≤ 49/22 := by
    by_contra hc
    have hc' : (49/22 : ℝ) ≤ Real.exp (4/5) := le_of_lt (lt_of_not_ge hc)
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤49/22) hc' 5
    rw [he5] at hh
    norm_num at hh
    linarith
  have hp : Real.pi ≤ 22/7 := by linarith [Real.pi_lt_d4]
  have hq : Real.exp (4/5 : ℝ) ≤ 7/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    have hh := mul_le_mul he hp Real.pi_pos.le (by norm_num : (0:ℝ)≤49/22)
    norm_num at hh
    linarith only [hh]
  have hlog : (4/5 : ℝ) ≤ Real.log (7/Real.pi) := by
    apply Real.exp_le_exp.mp
    rwa [Real.exp_log (by positivity : (0:ℝ)<7/Real.pi)]
  unfold witnessCenter
  linarith only [hlog]


/-- Even eighth-degree test direction with sixth-degree coefficient one. -/
def witnessVector : Fin 5 → ℝ := ![-658560, 47040, -420, 1, -(1/1568)]

private theorem witnessVector_four : witnessVector 4 = -(1/1568 : ℝ) := rfl

private def directionalPolynomial (a s : ℝ) : ℝ :=
  let A : ℝ := -658560
  let B : ℝ := 47040
  let C : ℝ := -420
  let E : ℝ := -(1/1568)
  let R := fun k => (thetaPairRadialEvenPolynomial a k).eval s
  A^2*R 0 + 2*A*B*R 1 + (B^2+2*A*C)*R 2 +
    (2*A+2*B*C)*R 3 + (C^2+2*B+2*A*E)*R 4 +
    (2*C+2*B*E)*R 5 + (1+2*C*E)*R 6 + 2*E*R 7 + E^2*R 8

private theorem signed_pair_radial (a b k : ℕ) (x : ℝ) :
    (-1:ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) a b x =
      4*(thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x)*
        Real.exp (x-thetaCuspSingleAtomReflectionScale a x-thetaCuspSingleAtomReflectionScale b x)*
        (thetaPairRadialEvenPolynomial
          (thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x) k).eval
          (thetaCuspSingleAtomReflectionScale a x+thetaCuspSingleAtomReflectionScale b x) := by
  unfold thetaCuspAtomPairReflectionJet
  rw [thetaCuspAtomPairEvenJet_eq_radial]
  have he : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1:ℝ)^k*(-1:ℝ)^k)*
      (4*(thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x)*
        Real.exp (x-thetaCuspSingleAtomReflectionScale a x-thetaCuspSingleAtomReflectionScale b x)*
        (thetaPairRadialEvenPolynomial
          (thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x) k).eval
          (thetaCuspSingleAtomReflectionScale a x+thetaCuspSingleAtomReflectionScale b x)) := by ring
    _ = _ := by rw [he, one_mul]

private theorem retained_moment (k : ℕ) {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    (-1:ℝ)^k*thetaCuspTwoAtomReflectionJet (2*k) x =
      196*Real.exp (x-14)*((thetaPairRadialEvenPolynomial 49 k).eval 14+
        8*Real.exp (-21)*(thetaPairRadialEvenPolynomial 196 k).eval 35+
        16*Real.exp (-21)^2*(thetaPairRadialEvenPolynomial 784 k).eval 56) := by
  have hq2 : thetaCuspSingleAtomReflectionScale 2 x=28 := by
    have he : thetaCuspSingleAtomReflectionScale 2 x=4*thetaCuspSingleAtomReflectionScale 1 x := by
      unfold thetaCuspSingleAtomReflectionScale; norm_num; ring
    rw [he, hq]; norm_num
  have he35 : Real.exp (x-35)=Real.exp (x-14)*Real.exp (-21) := by
    rw [← Real.exp_add]; congr 1; ring
  have he56 : Real.exp (x-56)=Real.exp (x-14)*Real.exp (-21)^2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [thetaCuspTwoAtomReflectionJet_eq_pairs]
  simp only [mul_add, signed_pair_radial, hq, hq2]
  norm_num only
  rw [show x-7-7=x-14 by ring, show x-7-28=x-35 by ring,
    show x-28-7=x-35 by ring, show x-28-28=x-56 by ring, he35, he56]
  ring

private theorem first_mass_square {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    thetaCuspSourceTerm x 1^2=196*121*Real.exp (x-14) := by
  rw [thetaCuspSourceTerm_one_eq_scale_profile, hq, mul_pow]
  rw [pow_two, ← Real.exp_add, show (x/2-7)+(x/2-7)=x-14 by ring]
  ring

private theorem error_constant :
    (∑ i : Fin 5, ∑ j : Fin 5,
      |witnessVector i| * |witnessVector j| * ((2*(i.val+j.val)).factorial : ℝ) /
        (500000000 * (3/20 : ℝ)^(2*(i.val+j.val)))) ≤ 350000000000 := by
  norm_num [witnessVector, Fin.sum_univ_succ, Nat.factorial]

private theorem retained_core_lower {z : ℝ} (hz : 0 ≤ z) (hzU : z ≤ 1/1000000000) :
    500000000000*121 <
      directionalPolynomial 49 14 + 8*z*directionalPolynomial 196 35 +
        16*z^2*directionalPolynomial 784 56 := by
  have hsq := mul_self_le_mul_self hz hzU
  norm_num [directionalPolynomial, thetaPairRadialEvenPolynomial, thetaPairRadialEvenStep,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  nlinarith only [hz, hzU, hsq, sq_nonneg z]

/-- The complete even eighth-degree directional energy. -/
def sourceEnergy (x : ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, witnessVector i *
    ((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)*witnessVector j

private def retainedEnergy (x : ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, witnessVector i *
    ((-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*witnessVector j

private theorem energy_error_bound {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    |sourceEnergy x-retainedEnergy x| ≤ 350000000000*thetaCuspSourceTerm x 1^2 := by
  let f := thetaCuspSourceTerm x 1
  unfold sourceEnergy retainedEnergy
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5, |witnessVector i| * |witnessVector j| *
        (((2*(i.val+j.val)).factorial:ℝ)*(f^2/500000000)/(3/20)^(2*(i.val+j.val))) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      have hb := native_twoAtom_cauchy_error (2*(i.val+j.val)) (by rw [hq]; norm_num)
      have he (a b : ℝ) : witnessVector i*((-1:ℝ)^(i.val+j.val)*a)*witnessVector j-
          witnessVector i*((-1:ℝ)^(i.val+j.val)*b)*witnessVector j =
          witnessVector i*witnessVector j*(-1:ℝ)^(i.val+j.val)*(a-b) := by ring
      rw [he]
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      exact mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i : Fin 5, ∑ j : Fin 5,
        |witnessVector i| * |witnessVector j| * ((2*(i.val+j.val)).factorial:ℝ) /
        (500000000*(3/20:ℝ)^(2*(i.val+j.val))))*f^2 := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 350000000000*f^2 := mul_le_mul_of_nonneg_right error_constant (sq_nonneg f)

private theorem retained_energy_eq {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    retainedEnergy x = 196*Real.exp (x-14)*
      (directionalPolynomial 49 14 + 8*Real.exp (-21)*directionalPolynomial 196 35 +
        16*Real.exp (-21)^2*directionalPolynomial 784 56) := by
  unfold retainedEnergy
  simp only [retained_moment _ hq]
  norm_num [Fin.sum_univ_succ, witnessVector, directionalPolynomial]
  ring

private theorem retained_core_upper {z : ℝ} (hz : 0 ≤ z) (hzU : z ≤ 1/1000000000) :
    directionalPolynomial 49 14 + 8*z*directionalPolynomial 196 35 +
        16*z^2*directionalPolynomial 784 56 < 2000000000000*121 := by
  have hsq := mul_self_le_mul_self hz hzU
  norm_num [directionalPolynomial, thetaPairRadialEvenPolynomial, thetaPairRadialEvenStep,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  nlinarith only [hz, hzU, hsq, sq_nonneg z]

private theorem source_energy_bounds :
    150000000000*thetaCuspSourceTerm witnessCenter 1^2 < sourceEnergy witnessCenter ∧
    sourceEnergy witnessCenter < 2350000000000*thetaCuspSourceTerm witnessCenter 1^2 := by
  have hlo := mul_lt_mul_of_pos_left
    (retained_core_lower (Real.exp_pos (-21)).le second_decay_bound)
    (show 0 < 196*Real.exp (witnessCenter-14) by positivity)
  have hhi := mul_lt_mul_of_pos_left
    (retained_core_upper (Real.exp_pos (-21)).le second_decay_bound)
    (show 0 < 196*Real.exp (witnessCenter-14) by positivity)
  have he := energy_error_bound witness_scale
  have hl := (neg_le_abs (sourceEnergy witnessCenter-retainedEnergy witnessCenter)).trans he
  have hu := (le_abs_self (sourceEnergy witnessCenter-retainedEnergy witnessCenter)).trans he
  rw [retained_energy_eq witness_scale] at hl hu
  rw [first_mass_square witness_scale] at hl hu ⊢
  constructor <;> nlinarith only [hlo, hhi, hl, hu]

private theorem first_mass_pos : 0 < thetaCuspSourceTerm witnessCenter 1^2 := by
  rw [first_mass_square witness_scale]
  positivity

private theorem compensation_negative : thetaCuspCenterCompensationSource witnessCenter < 0 := by
  have hg := compensation_upper witness_scale witness_center_lower
  nlinarith only [hg, first_mass_pos]

/-- The native source remains strictly positive in the obstructing even direction. -/
theorem source_direction_positive : 0 < sourceEnergy witnessCenter := by
  have h := source_energy_bounds.1
  nlinarith only [h, first_mass_pos]

/-- Retaining the fixed fourth correction makes this complete-source direction negative. -/
theorem inherited_direction_negative :
    sourceEnergy witnessCenter +
      1000000000000*thetaCuspCenterCompensationSource witnessCenter < 0 := by
  have hu := source_energy_bounds.2
  have hg := compensation_upper witness_scale witness_center_lower
  nlinarith only [hu, hg, first_mass_pos]

/-- Every nonnegative fifth-diagonal correction preserves the negative direction. -/
theorem inherited_extension_direction_negative {D : ℝ} (hD : 0 ≤ D) :
    sourceEnergy witnessCenter +
      1000000000000*thetaCuspCenterCompensationSource witnessCenter +
      D*thetaCuspCenterCompensationSource witnessCenter*(witnessVector 4)^2 < 0 := by
  have hn := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hD compensation_negative.le) (sq_nonneg (witnessVector 4))
  linarith only [inherited_direction_negative, hn]

/-- Exact positive capacity of the native source against the inherited load. -/
def correctionCapacity : ℝ :=
  sourceEnergy witnessCenter / (-thetaCuspCenterCompensationSource witnessCenter)

theorem correctionCapacity_bounds : 0 < correctionCapacity ∧ correctionCapacity < 1000000000000 := by
  have hd : 0 < -thetaCuspCenterCompensationSource witnessCenter := neg_pos.mpr compensation_negative
  constructor
  · exact div_pos source_direction_positive hd
  · apply (div_lt_iff₀ hd).mpr
    linarith only [inherited_direction_negative]

theorem source_direction_positive_iff (C : ℝ) :
    0 < sourceEnergy witnessCenter + C*thetaCuspCenterCompensationSource witnessCenter ↔
      C < correctionCapacity := by
  have hd : 0 < -thetaCuspCenterCompensationSource witnessCenter := neg_pos.mpr compensation_negative
  rw [correctionCapacity, lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith only [h]

/-- The two inherited loads share one exact finite directional capacity. -/
theorem two_loads_positive_iff (C D : ℝ) :
    0 < sourceEnergy witnessCenter +
      C*thetaCuspCenterCompensationSource witnessCenter +
      D*thetaCuspCenterCompensationSource witnessCenter*(witnessVector 4)^2 ↔
      C + D/(1568:ℝ)^2 < correctionCapacity := by
  have he : sourceEnergy witnessCenter +
      C*thetaCuspCenterCompensationSource witnessCenter +
      D*thetaCuspCenterCompensationSource witnessCenter*(witnessVector 4)^2 =
      sourceEnergy witnessCenter +
        (C + D/(1568:ℝ)^2)*thetaCuspCenterCompensationSource witnessCenter := by
    rw [witnessVector_four]
    ring
  rw [he, source_direction_positive_iff]


/-- Radius of the fixed scale-seven source center. -/
def witnessRadius : ℝ := 2*witnessCenter

private theorem witnessRadius_pos : 0 < witnessRadius := by
  unfold witnessRadius
  linarith only [witness_center_lower]

private theorem witnessRadius_le : witnessRadius ≤ 7/8 := by
  have h := sixteen_mul_center_le_firstAtomScale
    (show 0 ≤ witnessCenter by linarith only [witness_center_lower])
  rw [witness_scale] at h
  unfold witnessRadius
  linarith only [h]

private theorem witness_half : witnessRadius/2 = witnessCenter := by
  unfold witnessRadius
  ring

private theorem aperture_slack_lt {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t*Real.cosh t-Real.sinh t < Real.sinh t := by
  have he : Real.exp t < 3 := (Real.exp_lt_exp.mpr ht1).trans
    (by linarith only [Real.exp_one_lt_d9])
  have hn : Real.exp (-t) ≤ 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (neg_nonpos.mpr ht.le))
  have hc : Real.cosh t < 2 := by
    rw [Real.cosh_eq]
    linarith only [he, hn]
  have hm := mul_lt_mul_of_pos_left hc ht
  have hs := Real.self_le_sinh_iff.mpr ht.le
  linarith only [hm, hs]

/-- Positive aperture weight at the fixed source center. -/
def witnessWeight (a : ℝ) : ℝ := witnessRadius*Real.sinh (a*witnessRadius)

private theorem witnessWeight_pos {a : ℝ} (ha : 0 < a) : 0 < witnessWeight a :=
  mul_pos witnessRadius_pos (Real.sinh_pos_iff.mpr (mul_pos ha witnessRadius_pos))

/-- The actual flux derivative supplying either corrected diagonal. -/
def weightedLoad (a : ℝ) : ℝ := deriv (thetaCuspCenterCompensationFlux a) witnessRadius

private theorem weightedLoad_upper {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    weightedLoad a ≤ -3*witnessWeight a*thetaCuspSourceTerm witnessCenter 1^2 := by
  let r := witnessRadius
  let F := thetaCuspFullSource witnessCenter
  let f := thetaCuspSourceTerm witnessCenter 1
  let t := a*r
  have hr : 0 < r := witnessRadius_pos
  have ht : 0 < t := mul_pos ha hr
  have ht1 : t < 1 := by
    have h := mul_lt_mul_of_pos_right haU hr
    change a*r < (1/2)*r at h
    have hb : r ≤ 7/8 := witnessRadius_le
    dsimp only [t]
    linarith only [h, hb]
  have hw := witnessWeight_pos ha
  have hs := mul_le_mul_of_nonneg_left (aperture_slack_lt ht ht1).le
    (show 0 ≤ r*F^2 by positivity)
  have hg := mul_le_mul_of_nonneg_left
    (compensation_upper witness_scale witness_center_lower) hw.le
  have hmass := (thetaCuspFullSource_mass_slope_le_scaleSeven
    (x := witnessCenter) (by rw [witness_scale])).1
  have hsq := mul_self_le_mul_self (thetaCuspFullSource_pos_all witnessCenter).le hmass
  have hsqw := mul_le_mul_of_nonneg_left hsq hw.le
  have hnonneg := mul_nonneg hw.le (sq_nonneg f)
  have he := deriv_thetaCuspCenterCompensationFlux_eq_source_add_slack a witnessRadius
  rw [witness_half] at he
  change weightedLoad a = witnessWeight a*thetaCuspCenterCompensationSource witnessCenter +
    r*F^2*(t*Real.cosh t-Real.sinh t) at he
  change weightedLoad a ≤ -3*witnessWeight a*f^2
  have hs' : r*F^2*(t*Real.cosh t-Real.sinh t) ≤ witnessWeight a*F^2 := by
    dsimp only [witnessWeight, t, r] at hs ⊢
    nlinarith only [hs]
  change witnessWeight a*thetaCuspCenterCompensationSource witnessCenter ≤
    witnessWeight a*(-(229/55)*f^2) at hg
  change witnessWeight a*(F*F) ≤
    witnessWeight a*((101/100)*f*((101/100)*f)) at hsqw
  nlinarith only [he, hs', hg, hsqw, hnonneg]

private theorem weightedLoad_neg {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    weightedLoad a < 0 := by
  have h := weightedLoad_upper ha haU
  have hp := mul_pos (witnessWeight_pos ha) first_mass_pos
  nlinarith only [h, hp]

/-- The inherited correction has a negative weighted direction at every critical aperture. -/
theorem weighted_inherited_direction_negative {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    witnessWeight a*sourceEnergy witnessCenter + 1000000000000*weightedLoad a < 0 := by
  have he := mul_lt_mul_of_pos_left source_energy_bounds.2 (witnessWeight_pos ha)
  have hg := mul_le_mul_of_nonneg_left (weightedLoad_upper ha haU)
    (by norm_num : (0 : ℝ) ≤ 1000000000000)
  have hp := mul_pos (witnessWeight_pos ha) first_mass_pos
  nlinarith only [he, hg, hp]

/-- A nonnegative load on the fifth diagonal cannot restore weighted pointwise positivity. -/
theorem weighted_inherited_extension_negative {a D : ℝ}
    (ha : 0 < a) (haU : a < 1/2) (hD : 0 ≤ D) :
    witnessWeight a*sourceEnergy witnessCenter + 1000000000000*weightedLoad a +
      D*weightedLoad a*(witnessVector 4)^2 < 0 := by
  have hn := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hD (weightedLoad_neg ha haU).le) (sq_nonneg (witnessVector 4))
  linarith only [weighted_inherited_direction_negative ha haU, hn]

/-- Exact directional capacity for the literal weighted flux derivative. -/
def weightedCapacity (a : ℝ) : ℝ :=
  witnessWeight a*sourceEnergy witnessCenter / (-weightedLoad a)

/-- Every critical aperture has a strictly positive capacity below the inherited coefficient. -/
theorem weightedCapacity_bounds {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    0 < weightedCapacity a ∧ weightedCapacity a < 1000000000000 := by
  have hd := neg_pos.mpr (weightedLoad_neg ha haU)
  constructor
  · exact div_pos (mul_pos (witnessWeight_pos ha) source_direction_positive) hd
  · apply (div_lt_iff₀ hd).mpr
    linarith only [weighted_inherited_direction_negative ha haU]

/-- The two diagonal coefficients share one exact positive weighted capacity. -/
theorem weighted_two_loads_positive_iff {a : ℝ} (ha : 0 < a) (haU : a < 1/2)
    (C D : ℝ) :
    0 < witnessWeight a*sourceEnergy witnessCenter + C*weightedLoad a +
      D*weightedLoad a*(witnessVector 4)^2 ↔ C+D/(1568 : ℝ)^2 < weightedCapacity a := by
  have hd := neg_pos.mpr (weightedLoad_neg ha haU)
  rw [weightedCapacity, lt_div_iff₀ hd]
  rw [witnessVector_four]
  norm_num
  constructor <;> intro h <;> nlinarith only [h]


private theorem native_matrix_energy (x : ℝ) :
    witnessVector ⬝ᵥ (RHTower.ThetaCuspGaussianLimit.nativeShiftedMatrix 5 0 x *ᵥ
      witnessVector) = sourceEnergy x := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, sourceEnergy,
    RHTower.ThetaCuspGaussianLimit.nativeShiftedMatrix, Nat.add_zero]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem diagonal_energy (C D G : ℝ) :
    witnessVector ⬝ᵥ (Matrix.diagonal (fun i : Fin 5 =>
      if i.val = 3 then C*G else if i.val = 4 then D*G else 0) *ᵥ witnessVector) =
      C*G + D*G*(witnessVector 4)^2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  rw [witnessVector_four]
  norm_num [Fin.sum_univ_succ, witnessVector]
  ring

private theorem matrix_energy (C D x : ℝ) :
    witnessVector ⬝ᵥ (evenFiveRepair C D x *ᵥ witnessVector) = sourceEnergy x +
      C*thetaCuspCenterCompensationSource x +
      D*thetaCuspCenterCompensationSource x*(witnessVector 4)^2 := by
  rw [evenFiveRepair, Matrix.add_mulVec, dotProduct_add,
    native_matrix_energy, diagonal_energy]
  ring

/-- No nonnegative fifth load repairs the inherited source at scale seven. -/
theorem inherited_matrix_not_posSemidef {D : ℝ} (hD : 0 ≤ D) :
    ¬ (evenFiveRepair 1000000000000 D witnessCenter).PosSemidef := by
  intro h
  have hh := h.dotProduct_mulVec_nonneg witnessVector
  simp only [star_trivial, matrix_energy] at hh
  exact (not_lt_of_ge hh) (inherited_extension_direction_negative hD)

/-- The origin-selected repair necessarily fails its intervening source comparison. -/
theorem selected_repair_schur_nonpos :
    evenFiveSchur witnessCenter +
      evenFiveRepairCoefficient*thetaCuspCenterCompensationSource witnessCenter ≤ 0 := by
  by_contra hn
  have hp := evenFiveRepair_posDef_of_schur
    (show 0 ≤ witnessCenter by linarith only [witness_center_lower]) (lt_of_not_ge hn)
  exact inherited_matrix_not_posSemidef evenFiveRepairCoefficient_pos.le hp.posSemidef

private theorem weighted_matrix_energy (a C D : ℝ) :
    witnessVector ⬝ᵥ (centerEvenFiveRepair a C D witnessRadius *ᵥ witnessVector) =
      witnessWeight a*sourceEnergy witnessCenter + C*weightedLoad a +
      D*weightedLoad a*(witnessVector 4)^2 := by
  have he : centerEvenFiveRepair a C D witnessRadius =
      witnessWeight a • RHTower.ThetaCuspGaussianLimit.nativeShiftedMatrix 5 0 witnessCenter +
        Matrix.diagonal (fun i : Fin 5 =>
          if i.val = 3 then C*weightedLoad a else if i.val = 4 then D*weightedLoad a else 0) := by
    ext i j
    simp only [centerEvenFiveRepair, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      RHTower.ThetaCuspGaussianLimit.nativeShiftedMatrix, Nat.add_zero,
      witnessWeight, weightedLoad, witness_half]
    ring
  rw [he, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    native_matrix_energy, diagonal_energy]
  ring

/-- The actual zero-flux representative fails pointwise positivity at every critical aperture. -/
theorem weighted_inherited_matrix_not_posSemidef {a D : ℝ}
    (ha : 0 < a) (haU : a < 1/2) (hD : 0 ≤ D) :
    ¬ (centerEvenFiveRepair a 1000000000000 D witnessRadius).PosSemidef := by
  intro h
  have hh := h.dotProduct_mulVec_nonneg witnessVector
  simp only [star_trivial, weighted_matrix_energy] at hh
  exact (not_lt_of_ge hh) (weighted_inherited_extension_negative ha haU hD)


private theorem weightedLoad_eq (a : ℝ) :
    weightedLoad a = witnessWeight a*thetaCuspCenterCompensationSource witnessCenter +
      witnessRadius*thetaCuspFullSource witnessCenter^2*
        (a*witnessRadius*Real.cosh (a*witnessRadius)-Real.sinh (a*witnessRadius)) := by
  have h := deriv_thetaCuspCenterCompensationFlux_eq_source_add_slack a witnessRadius
  rw [witness_half] at h
  exact h

private theorem aperture_slack_linear {t : ℝ} (ht : 0 < t) :
    t*Real.cosh t-Real.sinh t < t*Real.sinh t := by
  have hs := Real.sinh_pos_iff.mpr ht
  have h := RHTower.rcoth_lt_one_add_inv ht
  unfold RHTower.rcoth at h
  have hm := mul_lt_mul_of_pos_left ((div_lt_iff₀ hs).mp h) ht
  have he : t*((1+1/t)*Real.sinh t) = t*Real.sinh t+Real.sinh t := by
    field_simp [ht.ne']
  rw [he] at hm
  linarith only [hm]

private theorem weighted_direction_decomposition (a L : ℝ) :
    witnessWeight a*sourceEnergy witnessCenter + L*weightedLoad a =
      witnessWeight a*(sourceEnergy witnessCenter +
        L*thetaCuspCenterCompensationSource witnessCenter) +
      L*witnessRadius*thetaCuspFullSource witnessCenter^2*
        (a*witnessRadius*Real.cosh (a*witnessRadius)-Real.sinh (a*witnessRadius)) := by
  rw [weightedLoad_eq]
  ring

private theorem uniform_direction_pos_of_le {L : ℝ} (hL : L ≤ correctionCapacity)
    {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    0 < witnessWeight a*sourceEnergy witnessCenter + L*weightedLoad a := by
  have hw := witnessWeight_pos ha
  by_cases hL0 : L ≤ 0
  · exact add_pos_of_pos_of_nonneg (mul_pos hw source_direction_positive)
      (mul_nonneg_of_nonpos_of_nonpos hL0 (weightedLoad_neg ha haU).le)
  · have hLp : 0 < L := lt_of_not_ge hL0
    have hd := neg_pos.mpr compensation_negative
    have hb := (le_div_iff₀ hd).mp
      (show L ≤ sourceEnergy witnessCenter/(-thetaCuspCenterCompensationSource witnessCenter)
        from hL)
    have hbase : 0 ≤ sourceEnergy witnessCenter +
        L*thetaCuspCenterCompensationSource witnessCenter := by nlinarith only [hb]
    have hslack := sub_pos.mpr
      (RHTower.sinh_lt_mul_cosh (mul_pos ha witnessRadius_pos))
    have hPhi := sq_pos_of_pos (thetaCuspFullSource_pos_all witnessCenter)
    have hterm : 0 < L*witnessRadius*thetaCuspFullSource witnessCenter^2*
        (a*witnessRadius*Real.cosh (a*witnessRadius)-Real.sinh (a*witnessRadius)) := by
      exact mul_pos (mul_pos (mul_pos hLp witnessRadius_pos) hPhi) hslack
    rw [weighted_direction_decomposition]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hw.le hbase) hterm

/-- Strict positivity at every critical aperture includes the exact native capacity boundary. -/
theorem uniform_direction_positive_iff (L : ℝ) :
    (∀ a : ℝ, 0 < a → a < 1/2 →
      0 < witnessWeight a*sourceEnergy witnessCenter + L*weightedLoad a) ↔
      L ≤ correctionCapacity := by
  constructor
  · intro hall
    by_contra hn
    have hLC : correctionCapacity < L := lt_of_not_ge hn
    have hLp := correctionCapacity_bounds.1.trans hLC
    have hden := neg_pos.mpr compensation_negative
    have hb := (div_lt_iff₀ hden).mp
      (show sourceEnergy witnessCenter/(-thetaCuspCenterCompensationSource witnessCenter)<L
        from hLC)
    have hneg : sourceEnergy witnessCenter +
        L*thetaCuspCenterCompensationSource witnessCenter < 0 := by nlinarith only [hb]
    let d := -(sourceEnergy witnessCenter + L*thetaCuspCenterCompensationSource witnessCenter)
    let k := L*witnessRadius*thetaCuspFullSource witnessCenter^2
    have hd : 0 < d := neg_pos.mpr hneg
    have hk : 0 < k := mul_pos (mul_pos hLp witnessRadius_pos)
      (sq_pos_of_pos (thetaCuspFullSource_pos_all witnessCenter))
    let a := min (1/4 : ℝ) (d/(2*k))
    have ha : 0 < a := lt_min (by norm_num) (div_pos hd (by positivity))
    have haU : a < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
    have hasmall : a ≤ d/(2*k) := min_le_right _ _
    have hsmall : k*a ≤ d/2 := by
      have h := (le_div_iff₀ (show 0 < 2*k by positivity)).mp hasmall
      nlinarith only [h]
    have hslack := mul_le_mul_of_nonneg_left
      (aperture_slack_linear (mul_pos ha witnessRadius_pos)).le hk.le
    have he : witnessWeight a*sourceEnergy witnessCenter + L*weightedLoad a ≤
        witnessWeight a*(-d+k*a) := by
      rw [weighted_direction_decomposition]
      dsimp only [d, k, witnessWeight] at hslack ⊢
      nlinarith only [hslack]
    have hsmallneg : -d+k*a < 0 := by linarith only [hd, hsmall]
    have hfailure := he.trans_lt (mul_neg_of_pos_of_neg (witnessWeight_pos ha) hsmallneg)
    exact (not_lt_of_ge (hall a ha haU).le) hfailure
  · intro hL a ha haU
    exact uniform_direction_pos_of_le hL ha haU

/-- The aperture-uniform positive load region is a closed half-plane. -/
theorem weighted_two_loads_positive_at_every_aperture_iff (C D : ℝ) :
    (∀ a : ℝ, 0 < a → a < 1/2 →
      0 < witnessWeight a*sourceEnergy witnessCenter + C*weightedLoad a +
        D*weightedLoad a*(witnessVector 4)^2) ↔
      C+D/(1568 : ℝ)^2 ≤ correctionCapacity := by
  have he (a : ℝ) : witnessWeight a*sourceEnergy witnessCenter + C*weightedLoad a +
      D*weightedLoad a*(witnessVector 4)^2 =
      witnessWeight a*sourceEnergy witnessCenter + (C+D/(1568 : ℝ)^2)*weightedLoad a := by
    rw [witnessVector_four]
    ring
  simpa only [he] using uniform_direction_positive_iff (C+D/(1568 : ℝ)^2)

/-- Every positive aperture strictly enlarges the native directional capacity. -/
theorem weightedCapacity_exceeds_source {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    correctionCapacity < weightedCapacity a := by
  have h := uniform_direction_pos_of_le (L := correctionCapacity) le_rfl ha haU
  have hd := neg_pos.mpr (weightedLoad_neg ha haU)
  apply (lt_div_iff₀ hd).mpr
  nlinarith only [h]

end GaloisForLFunctions.ThetaCuspSections.EvenFiveBoundary
