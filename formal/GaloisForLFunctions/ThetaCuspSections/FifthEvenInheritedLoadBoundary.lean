import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRadialCoefficients
import GaloisForLFunctions.RHTower.CothInfra
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularCompensationDeterminant
import GaloisForLFunctions.ThetaCuspSections.FifthEvenSourceRepair
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspScaleSevenCompensationSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterCompensationTransitionSlack
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedCauchyTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspInheritedOddCompensationBoundary

/-!
# Constant load boundary for the fifth even theta source

Explicit even directions have positive complete-source energy at scale seven.
Their native and weighted capacities give exact positive load regions and
exclude large diagonal and coupled corrections. The eighth-degree capacity
is smaller than the fourth-head threshold at the origin.
Thus no constant fourth load and nonnegative fifth load give global source
positivity, including the weighted flux representative at each critical aperture.
The exact signed region preserving both boundary tests is nonempty.
A further Schur direction excludes a smaller coupled pair while retaining
positive native energy and exact native and weighted load capacities.
A polarized two-atom estimate controls every fifth-section entry at scale seven.
-/

noncomputable section
open Matrix Filter Topology RHTower Polynomial RHTower.ThetaCuspReflectedCauchyTail
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
        16*z^2*directionalPolynomial 784 56 < 1000000000000*121 := by
  have hsq := mul_self_le_mul_self hz hzU
  norm_num [directionalPolynomial, thetaPairRadialEvenPolynomial, thetaPairRadialEvenStep,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  nlinarith only [hz, hzU, hsq, sq_nonneg z]

private theorem source_energy_bounds :
    150000000000*thetaCuspSourceTerm witnessCenter 1^2 < sourceEnergy witnessCenter ∧
    sourceEnergy witnessCenter < 1350000000000*thetaCuspSourceTerm witnessCenter 1^2 := by
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


/-- Minimum fourth-diagonal load allowed by the literal origin head. -/
def originHeadThreshold : ℝ :=
  -thetaCuspNativeEvenFourSchur 0 / (3*thetaCuspFullSource 0^2)

private theorem originHeadThreshold_coefficient :
    3*originHeadThreshold + 1 = thetaCuspNativeEvenCompensationCoefficient := by
  unfold originHeadThreshold thetaCuspNativeEvenCompensationCoefficient
  rw [abs_of_neg thetaCuspNativeEvenFourSchur_zero_neg]
  field_simp [(thetaCuspFullSource_pos_all 0).ne']

private theorem originHeadThreshold_bounds :
    333000000000 < originHeadThreshold ∧ originHeadThreshold < 1000000000000 := by
  have h := thetaCuspNativeEvenCompensationCoefficient_bounds
  have he := originHeadThreshold_coefficient
  constructor <;> linarith only [h.1, h.2, he]

private theorem origin_modular_reserve {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) :
    0 < -HTGeometry.modularThetaEvenSeamFourPolynomial X -
      2000000000000*(HTGeometry.modularThetaEvenSeamHeadPolynomial X *
        HTGeometry.modularThetaEvenSeamMomentPolynomial 0 X) := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  rw [hX]
  norm_num [HTGeometry.modularThetaEvenSeamFourPolynomial, HTGeometry.modularThetaEvenSeamHeadPolynomial,
    HTGeometry.modularThetaEvenSeamMomentPolynomial]
  ring_nf
  linarith only [hz, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12, pow_nonneg hz 13, pow_nonneg hz 14, pow_nonneg hz 15, pow_nonneg hz 16, pow_nonneg hz 17, pow_nonneg hz 18, pow_nonneg hz 19, pow_nonneg hz 20]

private theorem seam_denominator_pos :
    0 < HTGeometry.modularThetaEvenSeamHeadPolynomial (thetaCuspSelfDualModularScale^2) *
      HTGeometry.modularThetaEvenSeamMomentPolynomial 0 (thetaCuspSelfDualModularScale^2) := by
  have hM : 0 < thetaCuspSelfDualThetaMass := by
    have h := thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
    linarith only [h]
  have hH := thetaCuspNativeEvenHead_zero_posDef.det_pos
  rw [thetaCuspNativeEvenHead_zero_det_eq_polynomial] at hH
  have hhead := (mul_pos_iff_of_pos_left (pow_pos hM 6)).mp hH
  have he : thetaCuspFullSource 0^2 = thetaCuspSelfDualThetaMass^2 *
      HTGeometry.modularThetaEvenSeamMomentPolynomial 0 (thetaCuspSelfDualModularScale^2) := by
    simpa [thetaCuspNativeReflectionJet, pow_two] using
      thetaCuspNativeEvenMoment_zero_eq_polynomial (0 : Fin 7)
  have hF := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
  rw [he] at hF
  exact mul_pos hhead ((mul_pos_iff_of_pos_left (pow_pos hM 2)).mp hF)

private theorem origin_coefficient_lower :
    2000000000000 < thetaCuspNativeEvenCompensationCoefficient := by
  have hr := origin_modular_reserve thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
  have hd := seam_denominator_pos
  have hq : (2000000000000 : ℝ) <
      -HTGeometry.modularThetaEvenSeamFourPolynomial (thetaCuspSelfDualModularScale^2) /
        (HTGeometry.modularThetaEvenSeamHeadPolynomial (thetaCuspSelfDualModularScale^2) *
          HTGeometry.modularThetaEvenSeamMomentPolynomial 0 (thetaCuspSelfDualModularScale^2)) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith only [hr]
  rw [thetaCuspNativeEvenCompensationCoefficient_eq_modularRatio]
  rw [neg_div] at hq
  nlinarith only [hq]

private theorem originHeadThreshold_lower : 660000000000 < originHeadThreshold := by
  linarith only [origin_coefficient_lower, originHeadThreshold_coefficient]

private theorem weightedCapacity_upper {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    weightedCapacity a < 450000000000 := by
  have hd := neg_pos.mpr (weightedLoad_neg ha haU)
  apply (div_lt_iff₀ hd).mpr
  have hE := mul_lt_mul_of_pos_left source_energy_bounds.2 (witnessWeight_pos ha)
  have hG := weightedLoad_upper ha haU
  nlinarith only [hE,hG]

/-- The weighted capacity and origin threshold are separated by a strictly positive uniform gap. -/
theorem weighted_load_capacity_gap {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    weightedCapacity a + 210000000000 < originHeadThreshold := by
  linarith only [weightedCapacity_upper ha haU, originHeadThreshold_lower]

private theorem correctionCapacity_upper : correctionCapacity < 330000000000 := by
  have hd := neg_pos.mpr compensation_negative
  apply (div_lt_iff₀ hd).mpr
  have hE := source_energy_bounds.2
  have hG := compensation_upper witness_scale witness_center_lower
  nlinarith only [hE, hG, first_mass_pos]

/-- The origin requires strictly more load than the positive scale-seven direction can accept. -/
theorem native_load_capacity_gap : correctionCapacity + 330000000000 < originHeadThreshold := by
  linarith only [correctionCapacity_upper, originHeadThreshold_lower]

/-- The exact origin threshold classifies strict positivity of the fourth head. -/
theorem origin_head_posDef_iff (C : ℝ) :
    (thetaCuspNativeEvenFourCompensated C 0).PosDef ↔ originHeadThreshold < C := by
  rw [thetaCuspNativeEvenFourCompensated_posDef_iff le_rfl]
  have hd : 0 < 3*thetaCuspFullSource 0^2 := by
    have h := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
    positivity
  rw [originHeadThreshold, div_lt_iff₀ hd]
  norm_num only [thetaCuspCenterCompensationSource, zero_mul, mul_zero, add_zero]
  constructor <;> intro h <;> nlinarith only [h]

private theorem origin_load_needed {C : ℝ}
    (h : (thetaCuspNativeEvenFourCompensated C 0).PosSemidef) : originHeadThreshold ≤ C := by
  have hdet := h.det_nonneg
  rw [RHTower.ThetaCuspModularRatio.compensated_det_eq,
    thetaCuspNativeEvenFourDet_eq_head_mul_schur le_rfl] at hdet
  have hhead := thetaCuspNativeEvenHead_zero_posDef.det_pos
  have hs : 0 ≤ thetaCuspNativeEvenFourSchur 0 + C*thetaCuspCenterCompensationSource 0 := by
    by_contra hn
    have hm := mul_neg_of_pos_of_neg hhead (lt_of_not_ge hn)
    nlinarith only [hdet, hm]
  have hd : 0 < 3*thetaCuspFullSource 0^2 := by
    have h := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
    positivity
  rw [originHeadThreshold, div_le_iff₀ hd]
  norm_num only [thetaCuspCenterCompensationSource, zero_mul, mul_zero, add_zero] at hs
  nlinarith only [hs]

private theorem repair_four_head (C D x : ℝ) :
    (evenFiveRepair C D x).submatrix Fin.castSucc Fin.castSucc =
      thetaCuspNativeEvenFourCompensated C x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [evenFiveRepair, RHTower.ThetaCuspGaussianLimit.nativeShiftedMatrix,
      thetaCuspNativeEvenFourCompensated, Matrix.diagonal]

private theorem source_direction_nonneg_iff (C D : ℝ) :
    0 ≤ sourceEnergy witnessCenter + C*thetaCuspCenterCompensationSource witnessCenter +
      D*thetaCuspCenterCompensationSource witnessCenter*(witnessVector 4)^2 ↔
      C+D/(1568:ℝ)^2 ≤ correctionCapacity := by
  have hd := neg_pos.mpr compensation_negative
  rw [correctionCapacity, le_div_iff₀ hd, witnessVector_four]
  norm_num
  constructor <;> intro h <;> nlinarith only [h]

/-- A nonnegative fifth load prevents positivity at the origin and scale seven simultaneously,
regardless of the fourth load. -/
theorem constant_source_repair_fails (C : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ¬ ((evenFiveRepair C D 0).PosSemidef ∧
      (evenFiveRepair C D witnessCenter).PosSemidef) := by
  rintro ⟨h0,h7⟩
  have hh := h0.submatrix Fin.castSucc
  rw [repair_four_head] at hh
  have hC := origin_load_needed hh
  have hE := h7.dotProduct_mulVec_nonneg witnessVector
  simp only [star_trivial, matrix_energy] at hE
  have hcap := (source_direction_nonneg_iff C D).mp hE
  have hD' : 0 ≤ D/(1568:ℝ)^2 := div_nonneg hD (sq_nonneg _)
  linarith only [hC,hcap,hD',native_load_capacity_gap]

/-- The surviving signed load region has an open origin edge and a closed uniform-aperture edge. -/
theorem signed_boundary_region_iff (C D : ℝ) :
    ((thetaCuspNativeEvenFourCompensated C 0).PosDef ∧
      ∀ a : ℝ, 0 < a → a < 1/2 →
        0 < witnessWeight a*sourceEnergy witnessCenter + C*weightedLoad a +
          D*weightedLoad a*(witnessVector 4)^2) ↔
      (originHeadThreshold < C ∧ D ≤ (1568:ℝ)^2*(correctionCapacity-C)) := by
  rw [origin_head_posDef_iff, weighted_two_loads_positive_at_every_aperture_iff]
  have he : C+D/(1568:ℝ)^2 ≤ correctionCapacity ↔
      D ≤ (1568:ℝ)^2*(correctionCapacity-C) := by
    norm_num
    constructor <;> intro h <;> nlinarith only [h]
  rw [he]

/-- Both boundary tests can be strictly positive with a positive fourth load and negative fifth load.
This asserts the origin head and explicit direction, not the full fifth source. -/
theorem exists_signed_boundary_repair :
    ∃ C D : ℝ, 0 < C ∧ D < 0 ∧
      (thetaCuspNativeEvenFourCompensated C 0).PosDef ∧
      (∀ a : ℝ, 0 < a → a < 1/2 →
        0 < witnessWeight a*sourceEnergy witnessCenter + C*weightedLoad a +
          D*weightedLoad a*(witnessVector 4)^2) ∧
      0 < sourceEnergy witnessCenter + C*thetaCuspCenterCompensationSource witnessCenter +
        D*thetaCuspCenterCompensationSource witnessCenter*(witnessVector 4)^2 := by
  let C := originHeadThreshold+1
  let D := (1568:ℝ)^2*(correctionCapacity-C-1)
  have hC : originHeadThreshold < C := by dsimp [C]; linarith
  have hCp : 0 < C := by have h := originHeadThreshold_bounds.1; dsimp [C]; linarith
  have hD : D < 0 := by
    have h := native_load_capacity_gap
    dsimp only [C,D]
    nlinarith only [h]
  have hregion : D ≤ (1568:ℝ)^2*(correctionCapacity-C) := by dsimp [D]; nlinarith
  have hb := (signed_boundary_region_iff C D).mpr ⟨hC,hregion⟩
  refine ⟨C,D,hCp,hD,hb.1,hb.2,?_⟩
  rw [two_loads_positive_iff]
  have he : C+D/(1568:ℝ)^2 = correctionCapacity-1 := by dsimp [D]; ring
  rw [he]
  linarith


private theorem four_diagonal_energy (L : ℝ) (v : Fin 4 → ℝ) :
    v ⬝ᵥ (Matrix.diagonal (fun i : Fin 4 => if i.val = 3 then L else 0) *ᵥ v) =
      L*(v 3)^2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  rw [Finset.sum_eq_single (3 : Fin 4)]
  · norm_num
    ring
  · intro i hi hne
    have hv : i.val ≠ 3 := by
      intro he
      exact hne (Fin.ext he)
    simp only [hv, if_false, zero_mul, mul_zero]
  · simp

private theorem four_weighted_energy (a C D r : ℝ) (v : Fin 4 → ℝ) :
    v ⬝ᵥ ((centerEvenFiveRepair a C D r).submatrix Fin.castSucc Fin.castSucc *ᵥ v) =
      (r*Real.sinh (a*r))*(v ⬝ᵥ (thetaCuspNativeEvenFourCompensated C (r/2) *ᵥ v)) +
      C*(deriv (thetaCuspCenterCompensationFlux a) r -
        (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2))*(v 3)^2 := by
  have he : (centerEvenFiveRepair a C D r).submatrix Fin.castSucc Fin.castSucc =
      (r*Real.sinh (a*r)) • thetaCuspNativeEvenFourCompensated C (r/2) +
      Matrix.diagonal (fun i : Fin 4 => if i.val = 3 then
        C*(deriv (thetaCuspCenterCompensationFlux a) r -
          (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2)) else 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [centerEvenFiveRepair, thetaCuspNativeEvenFourCompensated,
        Matrix.diagonal, Matrix.smul_apply, smul_eq_mul]
    all_goals ring
  rw [he, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, four_diagonal_energy]

private theorem flux_slack_bounds {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    0 ≤ deriv (thetaCuspCenterCompensationFlux a) r -
      (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2) ∧
    deriv (thetaCuspCenterCompensationFlux a) r -
      (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2) ≤
      (r*Real.sinh (a*r))*(a*r)*thetaCuspFullSource (r/2)^2 := by
  have ht := mul_pos ha hr
  have h0 := sub_nonneg.mpr (RHTower.sinh_lt_mul_cosh ht).le
  have hU := (aperture_slack_linear ht).le
  have hF : 0 ≤ r*thetaCuspFullSource (r/2)^2 := mul_nonneg hr.le (sq_nonneg _)
  have h0' := mul_nonneg hF h0
  have hU' := mul_le_mul_of_nonneg_left hU hF
  rw [deriv_thetaCuspCenterCompensationFlux_eq_source_add_slack]
  constructor <;> nlinarith only [h0',hU']

private def upperHeadForm (a C r : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  v ⬝ᵥ (thetaCuspNativeEvenFourCompensated C (r/2) *ᵥ v) +
    |C| * (a*r)*thetaCuspFullSource (r/2)^2*(v 3)^2

private theorem weighted_head_le_upper {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (C D : ℝ) (v : Fin 4 → ℝ) :
    v ⬝ᵥ ((centerEvenFiveRepair a C D r).submatrix Fin.castSucc Fin.castSucc *ᵥ v) ≤
      (r*Real.sinh (a*r))*upperHeadForm a C r v := by
  obtain ⟨h0,hU⟩ := flux_slack_bounds ha hr
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C) h0
  have hCU := mul_le_mul_of_nonneg_left hU (abs_nonneg C)
  have h := mul_le_mul_of_nonneg_right (hC.trans hCU) (sq_nonneg (v 3))
  rw [four_weighted_energy]
  unfold upperHeadForm
  nlinarith only [h]

private theorem upperHeadForm_continuous (a C : ℝ) (v : Fin 4 → ℝ) :
    Continuous (fun r : ℝ => upperHeadForm a C r v) := by
  have hM := continuous_thetaCuspNativeEvenFourCompensated C
  have hF : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  unfold upperHeadForm
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- The aperture slack vanishes relative to its positive weight at the origin.
A continuous upper quadratic form transfers weighted positivity to the native origin head. -/
private theorem origin_head_of_weighted_positive {a C D : ℝ} (ha : 0 < a)
    (h : ∀ r : ℝ, 0 < r → (centerEvenFiveRepair a C D r).PosSemidef) :
    (thetaCuspNativeEvenFourCompensated C 0).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspNativeEvenFourCompensated, add_comm, and_comm]
  · intro v
    simp only [star_trivial]
    have hnonneg (r : ℝ) (hr : 0 < r) : 0 ≤ upperHeadForm a C r v := by
      have hh := ((h r hr).submatrix Fin.castSucc).dotProduct_mulVec_nonneg v
      simp only [star_trivial] at hh
      have hu := hh.trans (weighted_head_le_upper ha hr C D v)
      have hw : 0 < r*Real.sinh (a*r) :=
        mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
      by_contra hn
      exact (not_lt_of_ge hu) (mul_neg_of_pos_of_neg hw (lt_of_not_ge hn))
    have ht : Tendsto (fun r : ℝ => upperHeadForm a C r v) (𝓝[>] 0)
        (𝓝 (v ⬝ᵥ (thetaCuspNativeEvenFourCompensated C 0 *ᵥ v))) := by
      have hc := (upperHeadForm_continuous a C v).tendsto 0
      simpa only [upperHeadForm, zero_div, mul_zero, zero_mul, add_zero] using
        hc.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hnonneg r hr

private theorem weighted_direction_negative_of_origin {a C D : ℝ}
    (ha : 0 < a) (haU : a < 1/2) (hD : 0 ≤ D) (hC : originHeadThreshold ≤ C) :
    witnessWeight a*sourceEnergy witnessCenter + C*weightedLoad a +
      D*weightedLoad a*(witnessVector 4)^2 < 0 := by
  have hC0 : 660000000000 ≤ C := originHeadThreshold_lower.le.trans hC
  have hCw := mul_le_mul_of_nonpos_right hC0 (weightedLoad_neg ha haU).le
  have hE := mul_lt_mul_of_pos_left source_energy_bounds.2 (witnessWeight_pos ha)
  have hG := weightedLoad_upper ha haU
  have hp := mul_pos (witnessWeight_pos ha) first_mass_pos
  have hD0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hD (weightedLoad_neg ha haU).le)
    (sq_nonneg (witnessVector 4))
  nlinarith only [hCw,hE,hG,hp,hD0]

/-- No constant fourth load and nonnegative fifth load give a pointwise positive weighted
representative, at any critical aperture. -/
theorem constant_weighted_repair_fails {a D : ℝ}
    (ha : 0 < a) (haU : a < 1/2) (hD : 0 ≤ D) (C : ℝ) :
    ¬ ∀ r : ℝ, 0 < r → (centerEvenFiveRepair a C D r).PosSemidef := by
  intro h
  have hC := origin_load_needed (origin_head_of_weighted_positive ha h)
  have hw := (h witnessRadius witnessRadius_pos).dotProduct_mulVec_nonneg witnessVector
  simp only [star_trivial, weighted_matrix_energy] at hw
  exact (not_lt_of_ge hw) (weighted_direction_negative_of_origin ha haU hD hC)


private theorem fourth_retained_upper :
    thetaCuspTwoAtomReflectionJet 8 witnessCenter ≤
      2000000000*thetaCuspSourceTerm witnessCenter 1^2 := by
  have ht0 := (Real.exp_pos (-21 : ℝ)).le
  have ht := second_decay_bound
  have ht2 := mul_self_le_mul_self ht0 ht
  have hp : (thetaPairRadialEvenPolynomial 49 4).eval 14+
      8*Real.exp (-21)*(thetaPairRadialEvenPolynomial 196 4).eval 35+
      16*Real.exp (-21)^2*(thetaPairRadialEvenPolynomial 784 4).eval 56 ≤
        2000000000*121 := by
    norm_num [eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
      radialCoeffs_4_0,radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,
      radialCoeffs_4_4,radialCoeffs_4_5,radialCoeffs_4_6,radialCoeffs_4_7,
      radialCoeffs_4_8,radialCoeffs_4_9]
    nlinarith only [ht0,ht,ht2]
  have hr := retained_moment 4 witness_scale
  norm_num only [even_two, Even.neg_one_pow, one_mul] at hr
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 196*Real.exp (witnessCenter-14) by positivity)
  rw [hr,first_mass_square witness_scale]
  nlinarith only [hm]

private theorem fourth_moment_upper :
    thetaCuspNativeReflectionJet 8 witnessCenter <
      3000000000*thetaCuspSourceTerm witnessCenter 1^2 := by
  have herr := native_twoAtom_cauchy_error 8
    (show 5 ≤ thetaCuspSingleAtomReflectionScale 1 witnessCenter by rw [witness_scale]; norm_num)
  have hu := (le_abs_self (thetaCuspNativeReflectionJet 8 witnessCenter-
    thetaCuspTwoAtomReflectionJet 8 witnessCenter)).trans herr
  have hf := first_mass_pos
  have hret := fourth_retained_upper
  norm_num [Nat.factorial] at hu
  nlinarith only [hu,hret,hf]

/-- The fourth even source moment cannot pay a billion units of compensation at scale seven. -/
theorem fourth_moment_load_negative :
    thetaCuspNativeReflectionJet 8 witnessCenter+
      1000000000*thetaCuspCenterCompensationSource witnessCenter < 0 := by
  have hu := fourth_moment_upper
  have hf := first_mass_pos
  have hg := compensation_upper witness_scale witness_center_lower
  nlinarith only [hu,hg,hf]

/-- Every critical aperture has a negative fourth-moment direction at a billion units of load. -/
theorem fourth_moment_weighted_load_negative {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    witnessWeight a*thetaCuspNativeReflectionJet 8 witnessCenter+
      1000000000*weightedLoad a < 0 := by
  have hu := mul_lt_mul_of_pos_left fourth_moment_upper (witnessWeight_pos ha)
  have hg := weightedLoad_upper ha haU
  nlinarith only [hu,hg]

/-- Every larger common source load retains the negative fourth-moment direction. -/
theorem fourth_moment_load_negative_of_oneBillion_le {C : ℝ} (hC : 1000000000 ≤ C) :
    thetaCuspNativeReflectionJet 8 witnessCenter+
      C*thetaCuspCenterCompensationSource witnessCenter < 0 := by
  have hg := compensation_upper witness_scale witness_center_lower
  have hG : thetaCuspCenterCompensationSource witnessCenter ≤ 0 := by
    nlinarith only [hg,sq_nonneg (thetaCuspSourceTerm witnessCenter 1)]
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hC) hG
  nlinarith only [fourth_moment_load_negative,hm]

/-- Every larger common weighted load has the same negative coordinate. -/
theorem fourth_moment_weighted_load_negative_of_oneBillion_le {a C : ℝ}
    (ha : 0 < a) (haU : a < 1/2) (hC : 1000000000 ≤ C) :
    witnessWeight a*thetaCuspNativeReflectionJet 8 witnessCenter+
      C*weightedLoad a < 0 := by
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hC) (weightedLoad_neg ha haU).le
  nlinarith only [fourth_moment_weighted_load_negative ha haU,hm]


/-- The normalized sixth Hermite direction at variance fifty-six. -/
def sixthVector : Fin 4 → ℝ := ![-6272,336,-2,1/420]

private def sixthDirectionalPolynomial (a X : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, sixthVector i*sixthVector j *
    (thetaPairRadialEvenPolynomial a (i.val+j.val)).eval X

/-- Complete-source energy in the sixth-degree scale-seven direction. -/
def sixthEnergy (x : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, sixthVector i *
    ((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)*sixthVector j

private def sixthRetainedEnergy (x : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, sixthVector i *
    ((-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*sixthVector j

private theorem sixth_error_constant :
    (∑ i : Fin 4, ∑ j : Fin 4,
      |sixthVector i| * |sixthVector j| * ((2*(i.val+j.val)).factorial:ℝ) /
        (500000000*(3/20:ℝ)^(2*(i.val+j.val)))) ≤ 1000000 := by
  norm_num [sixthVector,Fin.sum_univ_succ,Nat.factorial]
private theorem sixth_retained_lower {z : ℝ} (hz : 0 ≤ z) (hzU : z ≤ 1/1000000000) :
    89000000*121 < sixthDirectionalPolynomial 49 14+8*z*sixthDirectionalPolynomial 196 35+16*z^2*sixthDirectionalPolynomial 784 56 := by
  have hsq := mul_self_le_mul_self hz hzU
  norm_num [sixthDirectionalPolynomial,sixthVector,Fin.sum_univ_succ,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
    radialCoeffs_0_0,radialCoeffs_0_1,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,
    radialCoeffs_1_3,radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,
    radialCoeffs_2_4,radialCoeffs_2_5,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,
    radialCoeffs_3_3,radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,
    radialCoeffs_4_0,radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,
    radialCoeffs_4_5,radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,
    radialCoeffs_5_0,radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,
    radialCoeffs_5_5,radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,
    radialCoeffs_5_10,radialCoeffs_5_11,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,
    radialCoeffs_6_3,radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,
    radialCoeffs_6_8,radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,
    radialCoeffs_6_13]
  nlinarith only [hz,hzU,hsq,sq_nonneg z]
private theorem sixth_retained_upper {z : ℝ} (hz : 0 ≤ z) (hzU : z ≤ 1/1000000000) :
    sixthDirectionalPolynomial 49 14+8*z*sixthDirectionalPolynomial 196 35+16*z^2*sixthDirectionalPolynomial 784 56 < 199000000*121 := by
  have hsq := mul_self_le_mul_self hz hzU
  norm_num [sixthDirectionalPolynomial,sixthVector,Fin.sum_univ_succ,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
    radialCoeffs_0_0,radialCoeffs_0_1,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,
    radialCoeffs_1_3,radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,
    radialCoeffs_2_4,radialCoeffs_2_5,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,
    radialCoeffs_3_3,radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,
    radialCoeffs_4_0,radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,
    radialCoeffs_4_5,radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,
    radialCoeffs_5_0,radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,
    radialCoeffs_5_5,radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,
    radialCoeffs_5_10,radialCoeffs_5_11,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,
    radialCoeffs_6_3,radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,
    radialCoeffs_6_8,radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,
    radialCoeffs_6_13]
  nlinarith only [hz,hzU,hsq,sq_nonneg z]
private theorem sixth_energy_error_bound {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    |sixthEnergy x-sixthRetainedEnergy x| ≤ 1000000*thetaCuspSourceTerm x 1^2 := by
  let f := thetaCuspSourceTerm x 1
  unfold sixthEnergy sixthRetainedEnergy
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, |sixthVector i| * |sixthVector j| *
        (((2*(i.val+j.val)).factorial:ℝ)*(f^2/500000000)/(3/20)^(2*(i.val+j.val))) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      have hb := native_twoAtom_cauchy_error (2*(i.val+j.val)) (by rw [hq]; norm_num)
      have he (a b : ℝ) : sixthVector i*((-1:ℝ)^(i.val+j.val)*a)*sixthVector j-
          sixthVector i*((-1:ℝ)^(i.val+j.val)*b)*sixthVector j =
          sixthVector i*sixthVector j*(-1:ℝ)^(i.val+j.val)*(a-b) := by ring
      rw [he]
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      exact mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i : Fin 4, ∑ j : Fin 4,
        |sixthVector i| * |sixthVector j| * ((2*(i.val+j.val)).factorial:ℝ) /
        (500000000*(3/20:ℝ)^(2*(i.val+j.val))))*f^2 := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 1000000*f^2 := mul_le_mul_of_nonneg_right sixth_error_constant (sq_nonneg f)

private theorem sixth_retained_energy_eq {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    sixthRetainedEnergy x = 196*Real.exp (x-14)*
      (sixthDirectionalPolynomial 49 14 + 8*Real.exp (-21)*sixthDirectionalPolynomial 196 35 +
        16*Real.exp (-21)^2*sixthDirectionalPolynomial 784 56) := by
  unfold sixthRetainedEnergy
  simp only [retained_moment _ hq]
  norm_num [Fin.sum_univ_succ, sixthVector, sixthDirectionalPolynomial]
  ring


/-- The complete sixth-degree energy is positive, but smaller than two hundred million first-atom squares. -/
theorem sixth_energy_bounds :
    88000000*thetaCuspSourceTerm witnessCenter 1^2 < sixthEnergy witnessCenter ∧
    sixthEnergy witnessCenter < 200000000*thetaCuspSourceTerm witnessCenter 1^2 := by
  have hlo := mul_lt_mul_of_pos_left
    (sixth_retained_lower (Real.exp_pos (-21)).le second_decay_bound)
    (show 0 < 196*Real.exp (witnessCenter-14) by positivity)
  have hhi := mul_lt_mul_of_pos_left
    (sixth_retained_upper (Real.exp_pos (-21)).le second_decay_bound)
    (show 0 < 196*Real.exp (witnessCenter-14) by positivity)
  have he := sixth_energy_error_bound witness_scale
  have hl := (neg_le_abs (sixthEnergy witnessCenter-sixthRetainedEnergy witnessCenter)).trans he
  have hu := (le_abs_self (sixthEnergy witnessCenter-sixthRetainedEnergy witnessCenter)).trans he
  rw [sixth_retained_energy_eq witness_scale] at hl hu
  rw [first_mass_square witness_scale] at hl hu ⊢
  constructor <;> nlinarith only [hlo,hhi,hl,hu]

/-- The sixth-degree source direction is strictly positive before compensation. -/
theorem sixth_energy_pos : 0 < sixthEnergy witnessCenter := by
  have h := sixth_energy_bounds.1
  nlinarith only [h,first_mass_pos]

private theorem sixth_compensation_lower :
    -(11/2 : ℝ)*thetaCuspSourceTerm witnessCenter 1^2 <
      thetaCuspCenterCompensationSource witnessCenter := by
  let x := witnessCenter
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  have hx : 0 < x := by dsimp [x]; linarith only [witness_center_lower]
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hq : thetaCuspSingleAtomReflectionScale 1 x=7 := witness_scale
  have hmass : f ≤ F := by
    have hR := (thetaCuspLikelihoodSourceRemainder_signed_bounds_of_seven_le
      (n := 0) (by norm_num) (x := x) (by rw [hq])).1
    simp only [pow_zero,one_mul,iteratedDeriv_zero] at hR
    have hz := thetaCuspFullSource_derivative_sub_first_eq 0 hx
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
      Nat.choose_self,Nat.cast_one,Nat.reduceSub,one_mul,iteratedDeriv_zero,add_zero,zero_add] at hz
    have hp := mul_nonneg hf.le hR
    change F-f=f*thetaCuspLikelihoodSourceRemainder x at hz
    linarith only [hp,hz]
  have hmassU : F ≤ (101/100)*f :=
    (thetaCuspFullSource_mass_slope_le_scaleSeven (by rw [hq])).1
  have hslope : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x = -(197/22 : ℝ)*f := by
    have hd := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
    rw [iteratedDeriv_one] at hd
    rw [hd]
    dsimp only [thetaCuspGaussianScaleJet,thetaCuspGaussianScaleMoment,f]
    rw [thetaCuspSourceTerm_one_eq_scale_profile,hq]
    ring
  have he := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by norm_num)
    (show 7 ≤ thetaCuspSingleAtomReflectionScale 1 x by rw [hq])
  simp only [pow_zero,one_mul] at he
  have hε : 36*regimeOneLikelihoodScale x ≤ 1/100 := by linarith only [he]
  have h1 := abs_thetaCuspFullSource_derivative_sub_first_le_effective 1 hx (by rw [hq]; norm_num)
  simp only [iteratedDeriv_one,pow_one,hq,hslope] at h1
  have hm := mul_le_mul_of_nonneg_right hε (show 0 ≤ 7*f by positivity)
  have hd : -(91/10 : ℝ)*f ≤ deriv thetaCuspFullSource x := by
    have hl := (abs_le.mp h1).1
    dsimp only [f] at hm ⊢
    nlinarith only [hl,hm,hf]
  have hxu : x ≤ 7/16 := by
    have h := witnessRadius_le
    unfold witnessRadius at h
    dsimp only [x]
    linarith only [h]
  have hs := mul_self_le_mul_self hf.le hmass
  have hFF := mul_le_mul_of_nonneg_right hmassU hf.le
  have hxFF := mul_le_mul_of_nonneg_left hFF hx.le
  have hxf := mul_le_mul_of_nonneg_right hxu (sq_nonneg f)
  have hprod := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*x*F by positivity)
  change -(11/2 : ℝ)*f^2 < 3*F^2+2*x*F*deriv thetaCuspFullSource x
  nlinarith only [hs,hxFF,hxf,hprod,sq_pos_of_pos hf]

/-- Exact native load capacity in the sixth-degree direction. -/
def sixthCapacity : ℝ := sixthEnergy witnessCenter / (-thetaCuspCenterCompensationSource witnessCenter)

/-- The sixth-degree direction allows fewer than fifty million units of source load. -/
theorem sixthCapacity_bounds : 16000000 < sixthCapacity ∧ sixthCapacity < 50000000 := by
  have hd := neg_pos.mpr compensation_negative
  constructor
  · rw [sixthCapacity,lt_div_iff₀ hd]
    have hE := sixth_energy_bounds.1
    have hG := sixth_compensation_lower
    nlinarith only [hE,hG]
  · rw [sixthCapacity,div_lt_iff₀ hd]
    have hE := sixth_energy_bounds.2
    have hG := compensation_upper witness_scale witness_center_lower
    nlinarith only [hE,hG,first_mass_pos]

/-- Exact half-plane preserving strict positivity in the sixth-degree direction. -/
theorem sixth_coupled_positive_iff (C D : ℝ) :
    0 < sixthEnergy witnessCenter+(C+D/176400)*thetaCuspCenterCompensationSource witnessCenter ↔
      C+D/176400 < sixthCapacity := by
  have hd := neg_pos.mpr compensation_negative
  rw [sixthCapacity,lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith only [h]

/-- Every nonnegative second load fails when the first coupled load reaches one hundred million. -/
theorem sixth_coupled_negative {C D : ℝ} (hC : 100000000 ≤ C) (hD : 0 ≤ D) :
    sixthEnergy witnessCenter+(C+D/176400)*thetaCuspCenterCompensationSource witnessCenter < 0 := by
  have hc : 50000000 < C+D/176400 := by linarith only [hC,hD]
  have hd := neg_pos.mpr compensation_negative
  have hb := (div_lt_iff₀ hd).mp (sixthCapacity_bounds.2.trans hc)
  nlinarith only [hb]

/-- Exact weighted load capacity in the sixth-degree direction. -/
def sixthWeightedCapacity (a : ℝ) : ℝ :=
  witnessWeight a*sixthEnergy witnessCenter / (-weightedLoad a)

/-- Positive aperture slack strictly increases the sixth-degree directional capacity. -/
theorem sixthWeightedCapacity_exceeds_source {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    sixthCapacity < sixthWeightedCapacity a := by
  have hd := neg_pos.mpr compensation_negative
  have hw := neg_pos.mpr (weightedLoad_neg ha haU)
  have hs := sub_pos.mpr (RHTower.sinh_lt_mul_cosh (mul_pos ha witnessRadius_pos))
  have hterm := mul_pos
    (mul_pos witnessRadius_pos (sq_pos_of_pos (thetaCuspFullSource_pos_all witnessCenter))) hs
  have hL : witnessWeight a*thetaCuspCenterCompensationSource witnessCenter < weightedLoad a := by
    rw [weightedLoad_eq]
    linarith only [hterm]
  rw [sixthCapacity,sixthWeightedCapacity,div_lt_div_iff₀ hd hw]
  have h := mul_lt_mul_of_pos_left hL sixth_energy_pos
  nlinarith only [h]

/-- Critical apertures admit fewer than seventy million units in this direction. -/
theorem sixthWeightedCapacity_bounds {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    16000000 < sixthWeightedCapacity a ∧ sixthWeightedCapacity a < 70000000 := by
  have hd := neg_pos.mpr (weightedLoad_neg ha haU)
  constructor
  · exact sixthCapacity_bounds.1.trans (sixthWeightedCapacity_exceeds_source ha haU)
  · rw [sixthWeightedCapacity,div_lt_iff₀ hd]
    have hE := mul_lt_mul_of_pos_left sixth_energy_bounds.2 (witnessWeight_pos ha)
    have hG := weightedLoad_upper ha haU
    have hf := mul_pos (witnessWeight_pos ha) first_mass_pos
    nlinarith only [hE,hG,hf]

/-- The weighted sixth-degree test also defines an exact half-plane. -/
theorem sixth_coupled_weighted_positive_iff {a : ℝ} (ha : 0 < a) (haU : a < 1/2) (C D : ℝ) :
    0 < witnessWeight a*sixthEnergy witnessCenter+(C+D/176400)*weightedLoad a ↔
      C+D/176400 < sixthWeightedCapacity a := by
  have hd := neg_pos.mpr (weightedLoad_neg ha haU)
  rw [sixthWeightedCapacity,lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith only [h]

/-- Nonnegative second loads also fail at every critical aperture when the first reaches one hundred million. -/
theorem sixth_coupled_weighted_negative {a C D : ℝ}
    (ha : 0 < a) (haU : a < 1/2) (hC : 100000000 ≤ C) (hD : 0 ≤ D) :
    witnessWeight a*sixthEnergy witnessCenter+(C+D/176400)*weightedLoad a < 0 := by
  have hc : 70000000 < C+D/176400 := by linarith only [hC,hD]
  have hd := neg_pos.mpr (weightedLoad_neg ha haU)
  have hb := (div_lt_iff₀ hd).mp ((sixthWeightedCapacity_bounds ha haU).2.trans hc)
  nlinarith only [hb]

/- The first-atom moments are normalized by its mass square at scale seven.
Subtract the fixed coupled load with compensation coefficient 229/55,
then eliminate its first two coordinates. A second Schur elimination
fixes a rational direction with last coordinate -1/1568. -/
private def schurFirstMoment (k : ℕ) : ℝ := (thetaPairRadialEvenPolynomial 49 k).eval 14 / 121
private def schurHeadDet : ℝ := schurFirstMoment 0*schurFirstMoment 2-schurFirstMoment 1^2
private def schurAdjPair (a b c e : ℝ) : ℝ := schurFirstMoment 2*a*c-schurFirstMoment 1*(a*e+b*c)+schurFirstMoment 0*b*e
private def schurFixedTailLoad : Matrix (Fin 3) (Fin 3) ℝ :=
 !![10000000,420*10000000,0;
    420*10000000,176400*10000000+1000000000000,1568*1000000000000;
    0,1568*1000000000000,2458624*1000000000000]
private def schurEntry (i j : Fin 3) : ℝ :=
 schurHeadDet*(schurFirstMoment (i.val+j.val+4)-(229/55)*schurFixedTailLoad i j)-
 schurAdjPair (schurFirstMoment (i.val+2)) (schurFirstMoment (i.val+3)) (schurFirstMoment (j.val+2)) (schurFirstMoment (j.val+3))
private def schurTwoDet : ℝ := schurEntry 0 0*schurEntry 1 1-schurEntry 0 1^2
private def schurTailTwo : ℝ := (schurEntry 1 1*schurEntry 0 2-schurEntry 0 1*schurEntry 1 2)/(1568*schurTwoDet)
private def schurTailThree : ℝ := (schurEntry 0 0*schurEntry 1 2-schurEntry 0 1*schurEntry 0 2)/(1568*schurTwoDet)
private def schurTailFour : ℝ := -1/1568
private def schurBorderZero : ℝ := schurFirstMoment 2*schurTailTwo+schurFirstMoment 3*schurTailThree+schurFirstMoment 4*schurTailFour
private def schurBorderOne : ℝ := schurFirstMoment 3*schurTailTwo+schurFirstMoment 4*schurTailThree+schurFirstMoment 5*schurTailFour
private def schurHeadZero : ℝ := -(schurFirstMoment 2*schurBorderZero-schurFirstMoment 1*schurBorderOne)/schurHeadDet
private def schurHeadOne : ℝ := -(-schurFirstMoment 1*schurBorderZero+schurFirstMoment 0*schurBorderOne)/schurHeadDet
/-- Rational direction obtained by eliminating the positive fourth head of the scale-seven upper core. -/
def schurWitness : Fin 5 → ℝ := ![schurHeadZero,schurHeadOne,schurTailTwo,schurTailThree,schurTailFour]
private def schurDirectionalPolynomial (a X : ℝ) : ℝ :=
 let P := fun k => (thetaPairRadialEvenPolynomial a k).eval X
 schurHeadZero^2*P 0+2*schurHeadZero*schurHeadOne*P 1+(schurHeadOne^2+2*schurHeadZero*schurTailTwo)*P 2+
 (2*schurHeadZero*schurTailThree+2*schurHeadOne*schurTailTwo)*P 3+(schurTailTwo^2+2*schurHeadZero*schurTailFour+2*schurHeadOne*schurTailThree)*P 4+
 (2*schurHeadOne*schurTailFour+2*schurTailTwo*schurTailThree)*P 5+(schurTailThree^2+2*schurTailTwo*schurTailFour)*P 6+2*schurTailThree*schurTailFour*P 7+schurTailFour^2*P 8
private def schurFixedLoadCost : ℝ := 10000000*(schurTailTwo+420*schurTailThree)^2+1000000000000*(schurTailThree+1568*schurTailFour)^2
private def schurError : ℝ :=
 ∑ i : Fin 5, ∑ j : Fin 5, |schurWitness i| * |schurWitness j| * ((2*(i.val+j.val)).factorial:ℝ) /
   (10000000000000*(3/20:ℝ)^(2*(i.val+j.val)))
private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k = radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)

private theorem schur_retained_positive {z : ℝ} (hz : 0 ≤ z) (hzU : z ≤ 1/1000000000) :
 121*schurError < schurDirectionalPolynomial 49 14+8*z*schurDirectionalPolynomial 196 35+16*z^2*schurDirectionalPolynomial 784 56 := by
  have hs := mul_self_le_mul_self hz hzU
  norm_num [schurDirectionalPolynomial,schurFixedLoadCost,schurError,schurWitness,schurHeadZero,
    schurHeadOne,schurBorderZero,schurBorderOne,schurTailTwo,schurTailThree,schurTailFour,
    schurTwoDet,Fin.sum_univ_succ,Nat.factorial,schurEntry,schurHeadDet,schurAdjPair,
    schurFirstMoment,schurFixedTailLoad,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,
    Matrix.vecTail,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,radialCoeffs_0_0,
    radialCoeffs_0_1,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,radialCoeffs_1_3,
    radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,radialCoeffs_2_4,
    radialCoeffs_2_5,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,radialCoeffs_3_3,
    radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,radialCoeffs_4_0,
    radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,radialCoeffs_4_5,
    radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,radialCoeffs_5_0,
    radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,radialCoeffs_5_5,
    radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,radialCoeffs_5_10,
    radialCoeffs_5_11,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,radialCoeffs_6_3,
    radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,radialCoeffs_6_8,
    radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,radialCoeffs_6_13,
    radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,
    radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,
    radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,
    radialCoeffs_7_15,radial_eight_coeff,radial_seven_zero_16,radial_seven_zero_17,
    radial_seven_zero_18,radial_seven_zero_19,radialStepCoeff,radialInnerCoeff]
  nlinarith only [hz,hzU,hs,sq_nonneg z]
private theorem schur_retained_corrected_negative {z : ℝ} (hz : 0 ≤ z) (hzU : z ≤ 1/1000000000) :
 schurDirectionalPolynomial 49 14+8*z*schurDirectionalPolynomial 196 35+16*z^2*schurDirectionalPolynomial 784 56+
 121*schurError-(229/55)*121*schurFixedLoadCost < 0 := by
  have hs := mul_self_le_mul_self hz hzU
  norm_num [schurDirectionalPolynomial,schurFixedLoadCost,schurError,schurWitness,schurHeadZero,
    schurHeadOne,schurBorderZero,schurBorderOne,schurTailTwo,schurTailThree,schurTailFour,
    schurTwoDet,Fin.sum_univ_succ,Nat.factorial,schurEntry,schurHeadDet,schurAdjPair,
    schurFirstMoment,schurFixedTailLoad,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,
    Matrix.vecTail,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,radialCoeffs_0_0,
    radialCoeffs_0_1,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,radialCoeffs_1_3,
    radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,radialCoeffs_2_4,
    radialCoeffs_2_5,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,radialCoeffs_3_3,
    radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,radialCoeffs_4_0,
    radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,radialCoeffs_4_5,
    radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,radialCoeffs_5_0,
    radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,radialCoeffs_5_5,
    radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,radialCoeffs_5_10,
    radialCoeffs_5_11,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,radialCoeffs_6_3,
    radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,radialCoeffs_6_8,
    radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,radialCoeffs_6_13,
    radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,
    radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,
    radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,
    radialCoeffs_7_15,radial_eight_coeff,radial_seven_zero_16,radial_seven_zero_17,
    radial_seven_zero_18,radial_seven_zero_19,radialStepCoeff,radialInnerCoeff]
  nlinarith only [hz,hzU,hs,sq_nonneg z]

/-- Coupled load seen by the Schur direction. -/
def schurLoad (C D : ℝ) : ℝ :=
 C*(schurWitness 2+420*schurWitness 3)^2+D*(schurWitness 3+1568*schurWitness 4)^2

/-- Complete-source energy in the Schur direction. -/
def schurEnergy (x : ℝ) : ℝ :=
 ∑ i : Fin 5, ∑ j : Fin 5, schurWitness i *
  ((-1:ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)*schurWitness j

private def schurRetainedEnergy (x : ℝ) : ℝ :=
 ∑ i : Fin 5, ∑ j : Fin 5, schurWitness i *
  ((-1:ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*schurWitness j

private theorem schur_energy_error_bound {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    |schurEnergy x-schurRetainedEnergy x| ≤ schurError*thetaCuspSourceTerm x 1^2 := by
  let f := thetaCuspSourceTerm x 1
  unfold schurEnergy schurRetainedEnergy
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5, |schurWitness i| * |schurWitness j| *
        (((2*(i.val+j.val)).factorial:ℝ)*(f^2/10000000000000)/(3/20)^(2*(i.val+j.val))) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      have hb := native_twoAtom_cauchy_error_of_seven_le (2*(i.val+j.val)) (by rw [hq])
      have he (a b : ℝ) : schurWitness i*((-1:ℝ)^(i.val+j.val)*a)*schurWitness j-
          schurWitness i*((-1:ℝ)^(i.val+j.val)*b)*schurWitness j =
          schurWitness i*schurWitness j*(-1:ℝ)^(i.val+j.val)*(a-b) := by ring
      rw [he]
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      exact mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i : Fin 5, ∑ j : Fin 5,
        |schurWitness i| * |schurWitness j| * ((2*(i.val+j.val)).factorial:ℝ) /
        (10000000000000*(3/20:ℝ)^(2*(i.val+j.val))))*f^2 := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = schurError*f^2 := rfl

private theorem schur_retained_energy_eq {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    schurRetainedEnergy x = 196*Real.exp (x-14)*
      (schurDirectionalPolynomial 49 14+8*Real.exp (-21)*schurDirectionalPolynomial 196 35+
        16*Real.exp (-21)^2*schurDirectionalPolynomial 784 56) := by
  unfold schurRetainedEnergy
  simp only [retained_moment _ hq]
  norm_num [Fin.sum_univ_succ,schurWitness,schurDirectionalPolynomial]
  ring

/-- The complete native source is strictly positive in the Schur direction. -/
theorem schur_energy_pos : 0 < schurEnergy witnessCenter := by
  have hp := mul_lt_mul_of_pos_left
    (schur_retained_positive (Real.exp_pos (-21)).le second_decay_bound)
    (show 0 < 196*Real.exp (witnessCenter-14) by positivity)
  have he := schur_energy_error_bound witness_scale
  have hret : schurError*thetaCuspSourceTerm witnessCenter 1^2 <
      schurRetainedEnergy witnessCenter := by
    rw [first_mass_square witness_scale,schur_retained_energy_eq witness_scale]
    nlinarith only [hp]
  have hlo := (abs_le.mp he).1
  linarith only [hret,hlo]

/-- The reduced coupled pair loses the full Schur direction at scale seven. -/
theorem reduced_schur_energy_negative :
    schurEnergy witnessCenter+schurLoad 10000000 1000000000000*
      thetaCuspCenterCompensationSource witnessCenter < 0 := by
  have hp := mul_lt_mul_of_pos_left
    (schur_retained_corrected_negative (Real.exp_pos (-21)).le second_decay_bound)
    (show 0 < 196*Real.exp (witnessCenter-14) by positivity)
  have he := schur_energy_error_bound witness_scale
  have hret : schurRetainedEnergy witnessCenter+
      schurError*thetaCuspSourceTerm witnessCenter 1^2-
      (229/55)*thetaCuspSourceTerm witnessCenter 1^2*schurFixedLoadCost < 0 := by
    rw [first_mass_square witness_scale,schur_retained_energy_eq witness_scale]
    nlinarith only [hp]
  have hQ : 0 ≤ schurFixedLoadCost := by unfold schurFixedLoadCost; positivity
  have hG := mul_le_mul_of_nonneg_right
    (compensation_upper witness_scale witness_center_lower) hQ
  have hu := (abs_le.mp he).2
  change schurEnergy witnessCenter+schurFixedLoadCost*
    thetaCuspCenterCompensationSource witnessCenter < 0
  nlinarith only [hret,hG,hu]

/-- Exact native capacity in the Schur direction. -/
def schurCapacity : ℝ := schurEnergy witnessCenter/(-thetaCuspCenterCompensationSource witnessCenter)

/-- The actual positive capacity lies below the reduced pair's load. -/
theorem schurCapacity_bounds : 0 < schurCapacity ∧ schurCapacity < schurLoad 10000000 1000000000000 := by
  have hd := neg_pos.mpr compensation_negative
  constructor
  · exact div_pos schur_energy_pos hd
  · rw [schurCapacity,div_lt_iff₀ hd]
    nlinarith only [reduced_schur_energy_negative]

/-- Exact half-plane preserving the complete Schur direction. -/
theorem schur_coupled_positive_iff (C D : ℝ) :
    0 < schurEnergy witnessCenter+schurLoad C D*thetaCuspCenterCompensationSource witnessCenter ↔
      schurLoad C D < schurCapacity := by
  have hd := neg_pos.mpr compensation_negative
  rw [schurCapacity,lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith only [h]

/-- Exact weighted capacity in the Schur direction. -/
def schurWeightedCapacity (a : ℝ) : ℝ := witnessWeight a*schurEnergy witnessCenter/(-weightedLoad a)

/-- Positive aperture slack increases the Schur-direction capacity. -/
theorem schurWeightedCapacity_exceeds_source {a : ℝ} (ha : 0 < a) (haU : a < 1/2) :
    schurCapacity < schurWeightedCapacity a := by
  have hd := neg_pos.mpr compensation_negative
  have hw := neg_pos.mpr (weightedLoad_neg ha haU)
  have hs := sub_pos.mpr (RHTower.sinh_lt_mul_cosh (mul_pos ha witnessRadius_pos))
  have hterm := mul_pos
    (mul_pos witnessRadius_pos (sq_pos_of_pos (thetaCuspFullSource_pos_all witnessCenter))) hs
  have hL : witnessWeight a*thetaCuspCenterCompensationSource witnessCenter < weightedLoad a := by
    rw [weightedLoad_eq]
    linarith only [hterm]
  rw [schurCapacity,schurWeightedCapacity,div_lt_div_iff₀ hd hw]
  have h := mul_lt_mul_of_pos_left hL schur_energy_pos
  nlinarith only [h]

/-- Exact weighted half-plane preserving the complete Schur direction. -/
theorem schur_coupled_weighted_positive_iff {a : ℝ} (ha : 0 < a) (haU : a < 1/2) (C D : ℝ) :
    0 < witnessWeight a*schurEnergy witnessCenter+schurLoad C D*weightedLoad a ↔
      schurLoad C D < schurWeightedCapacity a := by
  have hd := neg_pos.mpr (weightedLoad_neg ha haU)
  rw [schurWeightedCapacity,lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith only [h]

/-- The same pair fails at every sufficiently small positive aperture. -/
theorem reduced_schur_weighted_negative_small :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ ∀ a : ℝ, 0 < a → a < δ →
      witnessWeight a*schurEnergy witnessCenter+schurLoad 10000000 1000000000000*weightedLoad a < 0 := by
  let Q := schurLoad 10000000 1000000000000
  let E := schurEnergy witnessCenter
  let G := thetaCuspCenterCompensationSource witnessCenter
  let η := -(E+Q*G)
  let T := witnessRadius*thetaCuspFullSource witnessCenter^2*Q
  have hQ : 0 < Q := schurCapacity_bounds.1.trans schurCapacity_bounds.2
  have hη : 0 < η := neg_pos.mpr reduced_schur_energy_negative
  have hT : 0 < T := mul_pos (mul_pos witnessRadius_pos
    (sq_pos_of_pos (thetaCuspFullSource_pos_all witnessCenter))) hQ
  refine ⟨min (1/2) (η/(2*T)),lt_min (by norm_num) (div_pos hη (by positivity)),
    min_le_left _ _,fun a ha haδ => ?_⟩
  have haT : a*T < η/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*T by positivity)).mp (haδ.trans_le (min_le_right _ _))
    nlinarith only [hh]
  have hw := witnessWeight_pos ha
  have hs := (flux_slack_bounds ha witnessRadius_pos).2
  rw [witness_half] at hs
  change weightedLoad a-witnessWeight a*G ≤
    witnessWeight a*(a*witnessRadius)*thetaCuspFullSource witnessCenter^2 at hs
  have hm := mul_le_mul_of_nonneg_right hs hQ.le
  have hnegative : E+Q*G+a*T < 0 := by
    dsimp only [η] at haT hη
    linarith only [haT,hη]
  change witnessWeight a*E+Q*weightedLoad a < 0
  calc
    _ ≤ witnessWeight a*(E+Q*G+a*T) := by
      dsimp only [T] at hm ⊢
      nlinarith only [hm]
    _ < 0 := mul_neg_of_pos_of_neg hw hnegative

/-- Polarized radial polynomial for two fifth-section coefficient vectors. -/
def scaleSevenPolynomial (v w : Fin 5 → ℝ) (a X : ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, v i*w j*(thetaPairRadialEvenPolynomial a (i.val+j.val)).eval X

/-- Complete native bilinear form of the fifth even section. -/
def scaleSevenEnergy (v w : Fin 5 → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, v i*
    ((-1:ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)*w j

private def scaleSevenRetainedEnergy (v w : Fin 5 → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, v i*
    ((-1:ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*w j

/-- Cauchy remainder in a polarized fifth-section entry at scale seven. -/
def scaleSevenTailError (v w : Fin 5 → ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, |v i| * |w j| * ((2*(i.val+j.val)).factorial:ℝ) /
    (10000000000000*(3/20:ℝ)^(2*(i.val+j.val)))

/-- Explicit full-source error relative to the first atom, including both retained mixed terms. -/
def scaleSevenError (v w : Fin 5 → ℝ) : ℝ :=
  ((8/1000000000)*|scaleSevenPolynomial v w 196 35|+
    (16/1000000000^2)*|scaleSevenPolynomial v w 784 56|)/121+scaleSevenTailError v w

private theorem scaleSeven_cauchy_error (v w : Fin 5 → ℝ) {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    |scaleSevenEnergy v w x-scaleSevenRetainedEnergy v w x| ≤ scaleSevenTailError v w*thetaCuspSourceTerm x 1^2 := by
  let f := thetaCuspSourceTerm x 1
  unfold scaleSevenEnergy scaleSevenRetainedEnergy
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5, |v i| * |w j| *
        (((2*(i.val+j.val)).factorial:ℝ)*(f^2/10000000000000)/(3/20)^(2*(i.val+j.val))) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      have hb := native_twoAtom_cauchy_error_of_seven_le (2*(i.val+j.val)) (by rw [hq])
      have he (a b : ℝ) : v i*((-1:ℝ)^(i.val+j.val)*a)*w j-
          v i*((-1:ℝ)^(i.val+j.val)*b)*w j =
          v i*w j*(-1:ℝ)^(i.val+j.val)*(a-b) := by ring
      rw [he]
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      exact mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i : Fin 5, ∑ j : Fin 5,
        |v i| * |w j| * ((2*(i.val+j.val)).factorial:ℝ) /
        (10000000000000*(3/20:ℝ)^(2*(i.val+j.val))))*f^2 := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = scaleSevenTailError v w*f^2 := rfl

private theorem scaleSeven_retained_energy_eq (v w : Fin 5 → ℝ) {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    scaleSevenRetainedEnergy v w x = 196*Real.exp (x-14)*
      (scaleSevenPolynomial v w 49 14+8*Real.exp (-21)*scaleSevenPolynomial v w 196 35+
        16*Real.exp (-21)^2*scaleSevenPolynomial v w 784 56) := by
  unfold scaleSevenRetainedEnergy
  simp only [retained_moment _ hq]
  norm_num [Fin.sum_univ_succ,scaleSevenPolynomial]
  ring

/-- Every polarized entry has an explicit complete-source error bound at scale seven. -/
theorem scaleSeven_bilinear_error (v w : Fin 5 → ℝ) :
    |scaleSevenEnergy v w witnessCenter-
      (thetaCuspSourceTerm witnessCenter 1^2/121)*scaleSevenPolynomial v w 49 14| ≤
        scaleSevenError v w*thetaCuspSourceTerm witnessCenter 1^2 := by
  let f := thetaCuspSourceTerm witnessCenter 1
  let z := Real.exp (-21 : ℝ)
  let P := scaleSevenPolynomial v w
  have hz : 0 ≤ z := (Real.exp_pos _).le
  have hzU : z ≤ 1/1000000000 := second_decay_bound
  have hz2 := mul_self_le_mul_self hz hzU
  have hc := scaleSeven_cauchy_error v w witness_scale
  have hret : scaleSevenRetainedEnergy v w witnessCenter-(f^2/121)*P 49 14 =
      (f^2/121)*(8*z*P 196 35+16*z^2*P 784 56) := by
    dsimp only [f,P,z]
    rw [scaleSeven_retained_energy_eq v w witness_scale,first_mass_square witness_scale]
    ring
  have hpoly : |8*z*P 196 35+16*z^2*P 784 56| ≤
      (8/1000000000)*|P 196 35|+(16/1000000000^2)*|P 784 56| := by
    calc
      _ ≤ |8*z*P 196 35|+|16*z^2*P 784 56| := abs_add_le _ _
      _ = (8*z)*|P 196 35|+(16*z^2)*|P 784 56| := by
        simp only [abs_mul,abs_pow,abs_of_nonneg hz]
        norm_num
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (by nlinarith only [hzU]) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (by nlinarith only [hz2]) (abs_nonneg _))
  have hrem : |scaleSevenRetainedEnergy v w witnessCenter-(f^2/121)*P 49 14| ≤
      (f^2/121)*((8/1000000000)*|P 196 35|+(16/1000000000^2)*|P 784 56|) := by
    rw [hret,abs_mul,abs_of_nonneg (by positivity : 0 ≤ f^2/121)]
    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
  change |scaleSevenEnergy v w witnessCenter-(f^2/121)*P 49 14| ≤ scaleSevenError v w*f^2
  calc
    _ ≤ |scaleSevenEnergy v w witnessCenter-scaleSevenRetainedEnergy v w witnessCenter|+
        |scaleSevenRetainedEnergy v w witnessCenter-(f^2/121)*P 49 14| := by
      exact abs_sub_le _ _ _
    _ ≤ scaleSevenTailError v w*f^2+
        (f^2/121)*((8/1000000000)*|P 196 35|+(16/1000000000^2)*|P 784 56|) :=
      add_le_add hc hrem
    _ = scaleSevenError v w*f^2 := by unfold scaleSevenError; dsimp only [P]; ring

private theorem witness_center_le_401_div_1000 : witnessCenter ≤ (401/1000 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (401/500 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have he : (2229/1000 : ℝ) ≤ Real.exp (401/500) := by linarith only [h]
  have hpi : (31415/10000 : ℝ) < Real.pi := by linarith only [Real.pi_gt_d4]
  have hp := mul_le_mul_of_nonneg_right he Real.pi_pos.le
  have hq : 7/Real.pi ≤ Real.exp (401/500) := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith only [hp,hpi]
  have hl : Real.log (7/Real.pi) ≤ (401/500 : ℝ) := by
    apply Real.exp_le_exp.mp
    rwa [Real.exp_log (by positivity : (0:ℝ)<7/Real.pi)]
  unfold witnessCenter
  linarith only [hl]

/-- Loss obtained from the center, mass and first-derivative bounds at scale seven. -/
def scaleSevenCompensationLoss : ℝ :=
  2*(401/1000)*(1000001/1000000)*(1791/200)-3

/-- The complete compensation has the explicit normalized lower bound at scale seven. -/
theorem scaleSeven_compensation_lower :
    -scaleSevenCompensationLoss*thetaCuspSourceTerm witnessCenter 1^2 ≤
      thetaCuspCenterCompensationSource witnessCenter := by
  let x := witnessCenter
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  have hx : 0 < x := by dsimp [x]; linarith only [witness_center_lower]
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hq : thetaCuspSingleAtomReflectionScale 1 x=7 := witness_scale
  have hmass : f ≤ F := by
    have hR := (thetaCuspLikelihoodSourceRemainder_signed_bounds_of_seven_le
      (n := 0) (by norm_num) (x := x) (by rw [hq])).1
    simp only [pow_zero,one_mul,iteratedDeriv_zero] at hR
    have hz := thetaCuspFullSource_derivative_sub_first_eq 0 hx
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
      Nat.choose_self,Nat.cast_one,Nat.reduceSub,one_mul,iteratedDeriv_zero,add_zero,zero_add] at hz
    have hp := mul_nonneg hf.le hR
    change F-f=f*thetaCuspLikelihoodSourceRemainder x at hz
    linarith only [hp,hz]
  have he := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by norm_num)
    (show 7 ≤ thetaCuspSingleAtomReflectionScale 1 x by rw [hq])
  simp only [pow_zero,one_mul] at he
  have hmassU : F ≤ (1000001/1000000)*f := by
    have hε : 3*regimeOneLikelihoodScale x ≤ 1/1000000 := by linarith only [he]
    have h0 := abs_thetaCuspFullSource_derivative_sub_first_le_effective 0 hx (by norm_num [hq])
    simp only [iteratedDeriv_zero,pow_zero,mul_one] at h0
    have hm := mul_le_mul_of_nonneg_right hε hf.le
    have hu := (abs_le.mp h0).2
    change F-f ≤ 3*regimeOneLikelihoodScale x*f at hu
    nlinarith only [hu,hm]
  have hslope : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x = -(197/22 : ℝ)*f := by
    have hd := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
    rw [iteratedDeriv_one] at hd
    rw [hd]
    dsimp only [thetaCuspGaussianScaleJet,thetaCuspGaussianScaleMoment,f]
    rw [thetaCuspSourceTerm_one_eq_scale_profile,hq]
    ring
  have hε : 252*regimeOneLikelihoodScale x ≤ 1/100000 := by linarith only [he]
  have h1 := abs_thetaCuspFullSource_derivative_sub_first_le_effective 1 hx (by norm_num [hq])
  simp only [iteratedDeriv_one,pow_one,hq,hslope] at h1
  have hm := mul_le_mul_of_nonneg_right hε hf.le
  have hd : -(1791/200 : ℝ)*f ≤ deriv thetaCuspFullSource x := by
    have hl := (abs_le.mp h1).1
    dsimp only [f] at hm ⊢
    nlinarith only [hl,hm,hf]
  have hxu : x ≤ 401/1000 := witness_center_le_401_div_1000
  have hs := mul_self_le_mul_self hf.le hmass
  have hFF := mul_le_mul_of_nonneg_right hmassU hf.le
  have hxFF := mul_le_mul_of_nonneg_left hFF hx.le
  have hxf := mul_le_mul_of_nonneg_right hxu (sq_nonneg f)
  have hprod := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*x*F by positivity)
  change -(2*(401/1000)*(1000001/1000000)*(1791/200)-3)*f^2 ≤
    3*F^2+2*x*F*deriv thetaCuspFullSource x
  nlinarith only [hs,hxFF,hxf,hprod]


private theorem scaleSeven_exponential_lower : (25000000000/19:ℝ) ≤ Real.exp 21 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 21
  rw [← Real.exp_nat_mul] at hp
  simp only [Nat.cast_ofNat,mul_one] at hp
  exact (by norm_num : (25000000000/19:ℝ) ≤ (2.7182818283:ℝ)^21).trans hp

private theorem scaleSeven_exponential_upper : Real.exp 21 ≤ (4000000000/3:ℝ) := by
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 21
  rw [← Real.exp_nat_mul] at hp
  simp only [Nat.cast_ofNat,mul_one] at hp
  exact hp.trans (by norm_num : (2.7182818286:ℝ)^21 ≤ (4000000000/3:ℝ))

private theorem scaleSeven_ratio_bounds :
    (3/4000000000:ℝ) ≤ Real.exp (-21) ∧ Real.exp (-21) ≤ (19/25000000000:ℝ) := by
  rw [Real.exp_neg,inv_eq_one_div]
  constructor
  · have h := one_div_le_one_div_of_le (Real.exp_pos 21) scaleSeven_exponential_upper
    norm_num at h
    simpa only [one_div] using h
  · have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 25000000000/19)
      scaleSeven_exponential_lower
    norm_num at h
    simpa only [one_div] using h

/-- Rational two-atom model at the upper endpoint of the retained-ratio interval. -/
def scaleSevenRetainedModel (v w : Fin 5 → ℝ) : ℝ :=
  (scaleSevenPolynomial v w 49 14+
    8*(19/25000000000)*scaleSevenPolynomial v w 196 35+
    16*(19/25000000000:ℝ)^2*scaleSevenPolynomial v w 784 56)/121

/-- Error around the retained model, including the narrow ratio interval and the Cauchy tail. -/
def scaleSevenRetainedError (v w : Fin 5 → ℝ) : ℝ :=
  (8*((19/25000000000:ℝ)-(3/4000000000))*|scaleSevenPolynomial v w 196 35|+
    16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|scaleSevenPolynomial v w 784 56|)/121+
    scaleSevenTailError v w

/-- The complete fifth-section bilinear form is close to the rational retained two-atom model. -/
theorem scaleSeven_retained_bilinear_error (v w : Fin 5 → ℝ) :
    |scaleSevenEnergy v w witnessCenter-
      thetaCuspSourceTerm witnessCenter 1^2*scaleSevenRetainedModel v w| ≤
        scaleSevenRetainedError v w*thetaCuspSourceTerm witnessCenter 1^2 := by
  let f := thetaCuspSourceTerm witnessCenter 1
  let z := Real.exp (-21 : ℝ)
  let l : ℝ := 3/4000000000
  let r : ℝ := 19/25000000000
  let P := scaleSevenPolynomial v w
  have hz : 0 ≤ z := (Real.exp_pos _).le
  have hl : 0 ≤ l := by norm_num [l]
  have hzL : l ≤ z := scaleSeven_ratio_bounds.1
  have hzU : z ≤ r := scaleSeven_ratio_bounds.2
  have hz2L : l^2 ≤ z^2 := by nlinarith only [mul_self_le_mul_self hl hzL]
  have hz2U : z^2 ≤ r^2 := by nlinarith only [mul_self_le_mul_self hz hzU]
  have hdiff : |z-r| ≤ r-l := by
    rw [abs_of_nonpos (sub_nonpos.mpr hzU)]
    linarith only [hzL]
  have hdiff2 : |z^2-r^2| ≤ r^2-l^2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hz2U)]
    linarith only [hz2L]
  have hc := scaleSeven_cauchy_error v w witness_scale
  have hret : scaleSevenRetainedEnergy v w witnessCenter-f^2*scaleSevenRetainedModel v w =
      (f^2/121)*(8*(z-r)*P 196 35+16*(z^2-r^2)*P 784 56) := by
    dsimp only [f,z,r,P,scaleSevenRetainedModel]
    rw [scaleSeven_retained_energy_eq v w witness_scale,first_mass_square witness_scale]
    ring
  have hpoly : |8*(z-r)*P 196 35+16*(z^2-r^2)*P 784 56| ≤
      8*(r-l)*|P 196 35|+16*(r^2-l^2)*|P 784 56| := by
    calc
      _ ≤ |8*(z-r)*P 196 35|+|16*(z^2-r^2)*P 784 56| := abs_add_le _ _
      _ = 8*|z-r| * |P 196 35|+16*|z^2-r^2| * |P 784 56| := by
        simp only [abs_mul]
        norm_num
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (by norm_num)) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff2 (by norm_num)) (abs_nonneg _))
  have hrem : |scaleSevenRetainedEnergy v w witnessCenter-f^2*scaleSevenRetainedModel v w| ≤
      (f^2/121)*(8*(r-l)*|P 196 35|+16*(r^2-l^2)*|P 784 56|) := by
    rw [hret,abs_mul,abs_of_nonneg (by positivity : 0 ≤ f^2/121)]
    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
  change |scaleSevenEnergy v w witnessCenter-f^2*scaleSevenRetainedModel v w| ≤
    scaleSevenRetainedError v w*f^2
  calc
    _ ≤ |scaleSevenEnergy v w witnessCenter-scaleSevenRetainedEnergy v w witnessCenter|+
        |scaleSevenRetainedEnergy v w witnessCenter-f^2*scaleSevenRetainedModel v w| :=
      abs_sub_le _ _ _
    _ ≤ scaleSevenTailError v w*f^2+
        (f^2/121)*(8*(r-l)*|P 196 35|+16*(r^2-l^2)*|P 784 56|) := add_le_add hc hrem
    _ = scaleSevenRetainedError v w*f^2 := by
      dsimp only [scaleSevenRetainedError,P,r,l]
      ring

end GaloisForLFunctions.ThetaCuspSections.EvenFiveBoundary
