import GaloisForLFunctions.HTGeometry.CentralHermiteReflectionErrorBudget
import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomCentralFactorial
import GaloisForLFunctions.RHTower.ThetaCuspSharpFiniteCoolingTwelve
import GaloisForLFunctions.RHTower.ThetaCuspNativeOddSchurCompensation

/-!
# Complete reflection and compensation errors at scale eight

Exact first-atom moment bounds and the full likelihood measure control all seven
even reflection entries. The complete compensation error fits one last-coordinate
unit for the fixed coefficient 10^12. No source atom or pair is omitted.
-/

namespace RHTower
noncomputable section

private theorem firstScaled_lower_upper_five {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 6) :
    0 ≤ thetaCuspFirstAtomScaledEvenJet k.val x ∧
    thetaCuspFirstAtomScaledEvenJet k.val x ≤
      (3/2 : ℝ)*HTGeometry.centralGaussianMomentCeiling k.val*8^k.val := by
  have h7 : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hu := inverseScale_bounds_of_seven_le h7
  fin_cases k
  · have hx := regimeOne_pos_of_six_le (by linarith : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
    norm_num [thetaCuspFirstAtomScaledEvenJet,thetaCuspFirstAtomReflectionJet_zero,
      HTGeometry.centralGaussianMomentCeiling,hf]
  · rw [thetaCuspFirstAtomScaledEvenJet_1_eq_profile_of_seven_le h7]
    have h := HTGeometry.firstAtomOddScaleSeven_profile1_bounds hu.1 hu.2
    norm_num [HTGeometry.centralGaussianMomentCeiling] at *
    constructor <;> linarith
  · rw [thetaCuspFirstAtomScaledEvenJet_2_eq_profile_of_seven_le h7]
    have h := HTGeometry.firstAtomOddScaleSeven_profile2_bounds hu.1 hu.2
    norm_num [HTGeometry.centralGaussianMomentCeiling] at *
    constructor <;> linarith
  · rw [thetaCuspFirstAtomScaledEvenJet_3_eq_profile_of_seven_le h7]
    have h := HTGeometry.firstAtomOddScaleSeven_profile3_bounds hu.1 hu.2
    norm_num [HTGeometry.centralGaussianMomentCeiling] at *
    constructor <;> linarith
  · rw [thetaCuspFirstAtomScaledEvenJet_4_eq_profile_of_seven_le h7]
    have h := HTGeometry.firstAtomOddScaleSeven_profile4_bounds hu.1 hu.2
    norm_num [HTGeometry.centralGaussianMomentCeiling] at *
    constructor <;> linarith
  · rw [thetaCuspFirstAtomScaledEvenJet_5_eq_profile_of_seven_le h7]
    have h := HTGeometry.firstAtomOddScaleSeven_profile5_bounds hu.1 hu.2
    norm_num [HTGeometry.centralGaussianMomentCeiling] at *
    constructor <;> linarith

/-- All seven literal first-atom moments lie under the common Gaussian coefficient ceiling. -/
theorem firstScaled_lower_upper_six {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
    0 ≤ thetaCuspFirstAtomScaledEvenJet k.val x ∧
    thetaCuspFirstAtomScaledEvenJet k.val x ≤
      (3/2 : ℝ)*HTGeometry.centralGaussianMomentCeiling k.val*8^k.val := by
  by_cases hk : k.val < 6
  · exact firstScaled_lower_upper_five hq ⟨k.val,hk⟩
  have hk6 : k.val = 6 := by omega
  rw [hk6]
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  have hqpos : 0 < q := by dsimp [q]; linarith
  have hx := regimeOne_pos_of_six_le (by linarith : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
  have hfpos : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have hm (j : ℕ) : firstAtomSignedMoment j x = thetaCuspFirstAtomScaledEvenJet j x*(f^2*q^j) := by
    change (-1 : ℝ)^j*thetaCuspFirstAtomReflectionJet (2*j) x =
      ((-1 : ℝ)^j*thetaCuspFirstAtomReflectionJet (2*j) x/(f^2*q^j))*(f^2*q^j)
    have hd : f^2*q^j ≠ 0 := by positivity
    field_simp [hd]
  have hmnonneg (j : Fin 6) : 0 ≤ firstAtomSignedMoment j.val x := by
    rw [hm]
    exact mul_nonneg (firstScaled_lower_upper_five hq j).1 (by positivity)
  have h6nonneg : 0 ≤ firstAtomSignedMoment 6 x := by
    have h := firstAtomEvenEnergy_lower_of_four_le
      (by linarith : 4 ≤ thetaCuspSingleAtomReflectionScale 1 x) ![0,0,0,1]
    norm_num [firstAtomEvenEnergy,Fin.sum_univ_succ,Fin.succ] at h
    have hz : 0 ≤ 282*thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^6 := by positivity
    have hc : (![0,0,0,1] : Fin 4 → ℝ) 3 = 1 := rfl
    rw [hc,one_pow,mul_one] at h
    exact hz.trans h
  have h6central : firstAtomSignedMoment 6 x ≤ firstAtomCentralMoment 6 x := by
    norm_num [firstAtomCentralMoment]
    have h1 := hmnonneg 1
    have h2 := hmnonneg 2
    have h3 := hmnonneg 3
    have h4 := hmnonneg 4
    have h5 := hmnonneg 5
    norm_num at h1 h2 h3 h4 h5
    linarith only [h1,h2,h3,h4,h5]
  have hD : 72 ≤ (2*q-3)^2 := by dsimp [q]; nlinarith
  let C := Real.exp (x/2-q)^2*4*q^2*2724986880*q^6
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hupper : firstAtomSignedMoment 6 x ≤
      ((3/2 : ℝ)*10395*8^6)*(f^2*q^6) := by
    calc
      _ ≤ firstAtomCentralMoment 6 x := h6central
      _ = C*((2*q-3)^2+36) := by
        rw [firstAtomCentralMoment_eq]
        norm_num [centralGaussianCoefficient,C,q]
      _ ≤ C*((3/2 : ℝ)*(2*q-3)^2) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hD]) hC
      _ = _ := by
        dsimp [C,f,q]
        rw [thetaCuspSourceTerm_one_eq_scale_profile]
        ring
  rw [hm 6] at h6nonneg hupper
  have hd : 0 < f^2*q^6 := by positivity
  constructor
  · exact nonneg_of_mul_nonneg_left h6nonneg hd
  · norm_num [HTGeometry.centralGaussianMomentCeiling]
    norm_num at hupper
    exact le_of_mul_le_mul_right hupper hd

/-- A strict analytical exponential bound supplies the complete likelihood ceiling at scale eight. -/
theorem base_scale_eight_le :
    Real.exp (3*Real.pi)/399*Real.exp (-(3*(8 : ℝ))) ≤ 1/(800000000 : ℝ) := by
  have h24 : (25600000000 : ℝ) < Real.exp 24 := by
    have h := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (24 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith only [h]
  rw [show -(3*(8 : ℝ)) = -24 by norm_num,Real.exp_neg]
  rw [show Real.exp (3*Real.pi)/399*(Real.exp 24)⁻¹ =
    Real.exp (3*Real.pi)/(399*Real.exp 24) by field_simp]
  apply (div_le_iff₀ (by positivity : 0 < 399*Real.exp 24)).mpr
  nlinarith [exp_three_pi_lt_12704]

/-- The same complete exponential budget pays every required polynomial scale power. -/
theorem pow_mul_regimeOneLikelihoodScale_le_of_eight_le {j : ℕ} (hj : j ≤ 6) {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x^j*regimeOneLikelihoodScale x ≤
      (8 : ℝ)^j/(800000000 : ℝ) := by
  have hjr : (j : ℝ) ≤ 6 := by exact_mod_cast hj
  have h := pow_mul_regimeOneLikelihoodScale_le (k := j) (A₁ := 8)
    (by norm_num) (by linarith) hq
  apply h.trans
  have hb := mul_le_mul_of_nonneg_left base_scale_eight_le (show 0 ≤ (8 : ℝ)^j by positivity)
  simpa only [mul_one_div] using hb

/-- The exact even first-atom jet carries the common moment ceiling at its physical scale. -/
theorem abs_firstAtomReflectionJet_even_le_of_eight {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (j : Fin 7) :
    |thetaCuspFirstAtomReflectionJet (2*j.val) x| ≤
      ((3/2 : ℝ)*HTGeometry.centralGaussianMomentCeiling j.val)*
        thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^j.val := by
  have hc := firstScaled_lower_upper_six hq j
  have hx := regimeOne_pos_of_six_le (by linarith : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hd : 0 < thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^j.val := by positivity
  have he : |thetaCuspFirstAtomReflectionJet (2*j.val) x|/
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^j.val) =
      thetaCuspFirstAtomScaledEvenJet j.val x := by
    rw [← abs_of_nonneg hc.1]
    simp only [thetaCuspFirstAtomScaledEvenJet,abs_div,abs_mul,abs_pow,abs_neg,
      abs_one,one_pow,one_mul,abs_of_pos hd]
  have hh := (div_le_iff₀ hd).mp (he.trans_le hc.2)
  calc
    _ ≤ ((3/2 : ℝ)*HTGeometry.centralGaussianMomentCeiling j.val*8^j.val)*
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^j.val) := hh
    _ = _ := by rw [mul_pow]; ring

private theorem sum_range_even_only (f : ℕ → ℝ) (ho : ∀ j, f (2*j+1) = 0) (k : ℕ) :
    (∑ i ∈ Finset.range (2*k+1), f i) = ∑ j ∈ Finset.range (k+1), f (2*j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1)+1 = (2*k+1)+1+1 by omega,Finset.sum_range_succ,
      Finset.sum_range_succ,ho k,add_zero,ih,Finset.sum_range_succ]
    rw [show 2*k+1+1 = 2*(k+1) by omega]
    simp only [Finset.sum_range_succ]

private theorem reflection_scale_split (q : ℝ) (j r : ℕ) :
    (8*q)^j*(6*q)^(2*r) = (8*q)^(j+r)*(9/2 : ℝ)^r*q^r ∧
    (8*q)^j*(12*q)^(2*r) = (8*q)^(j+r)*(18 : ℝ)^r*q^r := by
  constructor
  · rw [pow_mul,show (6*q)^2 = (8*q)*((9/2 : ℝ)*q) by ring,
      mul_pow,mul_pow,pow_add]
    ring
  · rw [pow_mul,show (12*q)^2 = (8*q)*(18*q) by ring,
      mul_pow,mul_pow,pow_add]
    ring

private theorem reflection_error_factor_le {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (j r : ℕ) (hr : r ≤ 6) :
    (8*thetaCuspSingleAtomReflectionScale 1 x)^j*
      (2*(6*thetaCuspSingleAtomReflectionScale 1 x)^(2*r)*regimeOneLikelihoodScale x+
        (12*thetaCuspSingleAtomReflectionScale 1 x)^(2*r)*regimeOneLikelihoodScale x^2) ≤
    (8*thetaCuspSingleAtomReflectionScale 1 x)^(j+r)*
      (2*(36 : ℝ)^r/(800000000 : ℝ)+(144 : ℝ)^r/(800000000 : ℝ)^2) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let ε := regimeOneLikelihoodScale x
  have hqp : 0 ≤ q := by dsimp [q]; linarith
  have he : 0 ≤ ε := (regimeOneLikelihoodScale_pos x).le
  have hp : q^r*ε ≤ (8 : ℝ)^r/800000000 := pow_mul_regimeOneLikelihoodScale_le_of_eight_le hr hq
  have h0 : ε ≤ 1/800000000 := by
    simpa using pow_mul_regimeOneLikelihoodScale_le_of_eight_le (j := 0) (by omega) hq
  have hp2 : q^r*ε^2 ≤ (8 : ℝ)^r/800000000^2 := by
    have h := mul_le_mul hp h0 he (by positivity : 0 ≤ (8 : ℝ)^r/800000000)
    nlinarith only [h]
  have h36 : (9/2 : ℝ)^r*8^r = 36^r := by rw [← mul_pow]; norm_num
  have h144 : (18 : ℝ)^r*8^r = 144^r := by rw [← mul_pow]; norm_num
  have hs := reflection_scale_split q j r
  change (8*q)^j*(2*(6*q)^(2*r)*ε+(12*q)^(2*r)*ε^2) ≤ _
  calc
    _ = (8*q)^(j+r)*(2*((9/2 : ℝ)^r*(q^r*ε))+(18 : ℝ)^r*(q^r*ε^2)) := by
      calc
        _ = 2*((8*q)^j*(6*q)^(2*r))*ε+((8*q)^j*(12*q)^(2*r))*ε^2 := by ring
        _ = _ := by rw [hs.1,hs.2]; ring
    _ ≤ (8*q)^(j+r)*(2*((9/2 : ℝ)^r*(8^r/800000000))+(18 : ℝ)^r*(8^r/800000000^2)) := by
      gcongr
    _ = _ := by
      change (8*q)^(j+r)*_ = (8*q)^(j+r)*_
      congr 1
      simp only [← mul_div_assoc,h36,h144]

/-- Every complete even reflection entry through order twelve fits the scale-eight ceiling. -/
theorem abs_native_even_sub_first_le_centralErrorCeiling {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
    |(-1 : ℝ)^k.val*thetaCuspNativeReflectionJet (2*k.val) x-firstAtomSignedMoment k.val x| ≤
      thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^k.val*
        HTGeometry.centralErrorCeiling k.val := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let ε := regimeOneLikelihoodScale x
  let f := thetaCuspSourceTerm x 1
  have hqp : 0 ≤ q := by dsimp [q]; linarith
  have he : 0 ≤ ε := (regimeOneLikelihoodScale_pos x).le
  let summand := fun i : ℕ => ((2*k.val).choose i : ℝ)*|thetaCuspFirstAtomReflectionJet i x| *
    (2*(6*q)^(2*k.val-i)*ε+(12*q)^(2*k.val-i)*ε^2)
  have ho (j : ℕ) : summand (2*j+1) = 0 := by
    dsimp [summand]
    rw [thetaCuspFirstAtomReflectionJet_odd_zero (by exact ⟨j,by omega⟩) x]
    simp
  have herr := abs_thetaCuspNativeReflectionJet_sub_first_le_factored_twelve
    (n := 2*k.val) (by omega) hq
  change |thetaCuspNativeReflectionJet (2*k.val) x-thetaCuspFirstAtomReflectionJet (2*k.val) x| ≤
    ∑ i ∈ Finset.range (2*k.val+1), summand i at herr
  rw [sum_range_even_only summand ho k.val] at herr
  have hs : (∑ j ∈ Finset.range (k.val+1), summand (2*j)) ≤
      f^2*(8*q)^k.val*HTGeometry.scaleEightReflectionErrorMajorant k := by
    unfold HTGeometry.scaleEightReflectionErrorMajorant
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j ≤ k.val := by have := Finset.mem_range.mp hj; omega
    have hj7 : j < 7 := by omega
    have hjr : j+(k.val-j) = k.val := by omega
    have hjdiff : 2*k.val-2*j = 2*(k.val-j) := by omega
    have hb := abs_firstAtomReflectionJet_even_le_of_eight hq (⟨j,hj7⟩ : Fin 7)
    have hd : 0 ≤ (3/2 : ℝ)*HTGeometry.centralGaussianMomentCeiling j := by
      unfold HTGeometry.centralGaussianMomentCeiling
      split <;> norm_num
    have ht := reflection_error_factor_le hq j (k.val-j) (by omega)
    dsimp [summand]
    rw [hjdiff]
    calc
      _ ≤ ((2*k.val).choose (2*j) : ℝ)*
          (((3/2 : ℝ)*HTGeometry.centralGaussianMomentCeiling j)*f^2*(8*q)^j)*
          (2*(6*q)^(2*(k.val-j))*ε+(12*q)^(2*(k.val-j))*ε^2) := by
        gcongr
      _ = (((2*k.val).choose (2*j) : ℝ)*((3/2 : ℝ)*HTGeometry.centralGaussianMomentCeiling j)*f^2)*
          ((8*q)^j*(2*(6*q)^(2*(k.val-j))*ε+(12*q)^(2*(k.val-j))*ε^2)) := by ring
      _ ≤ (((2*k.val).choose (2*j) : ℝ)*((3/2 : ℝ)*HTGeometry.centralGaussianMomentCeiling j)*f^2)*
          ((8*q)^(j+(k.val-j))*(2*(36 : ℝ)^(k.val-j)/800000000+144^(k.val-j)/800000000^2)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by rw [hjr]; ring
  have hb := HTGeometry.scaleEightReflectionErrorMajorant_le k
  have hall := herr.trans (hs.trans (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ f^2*(8*q)^k.val)))
  have habs : |(-1 : ℝ)^k.val*thetaCuspNativeReflectionJet (2*k.val) x-firstAtomSignedMoment k.val x| =
      |thetaCuspNativeReflectionJet (2*k.val) x-thetaCuspFirstAtomReflectionJet (2*k.val) x| := by
    unfold firstAtomSignedMoment
    rw [← mul_sub,abs_mul,abs_pow]
    norm_num
  rw [habs]
  exact hall

/-- The full compensation differs from the first atom by at most one physical last-coordinate unit. -/
theorem abs_fullCompensation_sub_first_le_last_unit {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (1000000000000 : ℝ)*|thetaCuspCenterCompensationSource x-firstAtomCompensationSource x| ≤
      thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^6 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let R := thetaCuspLikelihoodSourceRemainder x
  let R' := deriv thetaCuspLikelihoodSourceRemainder x
  let ε := regimeOneLikelihoodScale x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have he : 0 ≤ ε := (regimeOneLikelihoodScale_pos x).le
  have heU : ε ≤ 1/800000000 := by
    simpa using pow_mul_regimeOneLikelihoodScale_le_of_eight_le (j := 0) (by omega) hq
  have he1 : ε ≤ 1 := by linarith
  have hR : 0 ≤ R ∧ R ≤ ε := by
    simpa using thetaCuspLikelihoodSourceRemainder_signed_bounds_of_eight_le (n := 0) (by omega) hq
  have hR' : |R'| ≤ 6*q*ε := by
    simpa [iteratedDeriv_one,q,R'] using
      abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_six_scale_twelve (n := 1) (by omega) hq
  have hF : thetaCuspFullSource x = f*(1+R) := by
    have h := thetaCuspFullSource_derivative_sub_first_eq 0 hx
    simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
      zero_add,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_self,iteratedDeriv_zero] at h
    change thetaCuspFullSource x-f = f*R at h
    linarith only [h]
  have hF' : deriv thetaCuspFullSource x =
      deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x*(1+R)+f*R' := by
    have h := thetaCuspFullSource_derivative_sub_first_eq 1 hx
    norm_num [Finset.sum_range_succ,iteratedDeriv_one] at h
    change deriv thetaCuspFullSource x-deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      f*R'+deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x*R at h
    linarith only [h]
  have hxq : x ≤ q/12 := by
    have h := twelve_mul_center_scale_le hx.le
    change 12*x*q ≤ q^2-9 at h
    have hh : x*q ≤ (q/12)*q := by nlinarith only [h]
    exact le_of_mul_le_mul_right hh hqp
  have hfp : |deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤ 12*q*f := by
    have h := abs_iteratedDeriv_firstAtom_le_effective 1 (x := x) (by norm_num; linarith)
    norm_num [iteratedDeriv_one] at h
    change |deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤ 3*(4*q)*f at h
    nlinarith only [h]
  have hG : |firstAtomCompensationSource x| ≤ 3*q^2*f^2 := by
    unfold firstAtomCompensationSource
    change |3*f^2+2*x*f*deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤ _
    calc
      _ ≤ |3*f^2|+|2*x*f*deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| := abs_add_le _ _
      _ = 3*f^2+2*x*f*|deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x| := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 3*f^2),abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ 2*x*f)]
      _ ≤ 3*f^2+2*(q/12)*f*(12*q*f) := by gcongr
      _ ≤ 3*q^2*f^2 := by
        have hq2 : 3 ≤ q^2 := by dsimp [q]; nlinarith
        have h := mul_nonneg (sq_nonneg f) (show 0 ≤ q^2-3 by linarith)
        nlinarith only [h]
  have hR0 := hR.1
  have hRR : |2*R+R^2| ≤ 3*ε := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2*R+R^2)]
    have hR1 : R ≤ 1 := hR.2.trans he1
    nlinarith [mul_nonneg hR.1 (sub_nonneg.mpr hR1)]
  have hR1 : |1+R| ≤ 2 := by rw [abs_of_nonneg (by linarith : 0 ≤ 1+R)]; linarith
  have hid : thetaCuspCenterCompensationSource x-firstAtomCompensationSource x =
      firstAtomCompensationSource x*(2*R+R^2)+2*x*f^2*(1+R)*R' := by
    unfold thetaCuspCenterCompensationSource
    rw [hF,hF']
    unfold firstAtomCompensationSource
    change 3*(f*(1+R))^2+2*x*(f*(1+R))*(deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x*(1+R)+f*R')-
      (3*f^2+2*x*f*deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x) = _
    ring
  have hb : |thetaCuspCenterCompensationSource x-firstAtomCompensationSource x| ≤ 11*q^2*ε*f^2 := by
    rw [hid]
    calc
      _ ≤ |firstAtomCompensationSource x*(2*R+R^2)|+|2*x*f^2*(1+R)*R'| := abs_add_le _ _
      _ = |firstAtomCompensationSource x| * |2*R+R^2|+2*x*f^2*|1+R| * |R'| := by
        rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*x*f^2)]
      _ ≤ (3*q^2*f^2)*(3*ε)+2*(q/12)*f^2*2*(6*q*ε) := by gcongr
      _ = _ := by ring
  have hq4 : (8 : ℝ)^4 ≤ q^4 := pow_le_pow_left₀ (by norm_num) hq 4
  have hnum : (1000000000000 : ℝ)*11/800000000 ≤ 8^6*q^4 := by nlinarith only [hq4]
  calc
    _ ≤ 1000000000000*(11*q^2*ε*f^2) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 1000000000000*(11*q^2*(1/800000000)*f^2) := by gcongr
    _ = (1000000000000*11/800000000)*(q^2*f^2) := by ring
    _ ≤ (8^6*q^4)*(q^2*f^2) := mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = _ := by change _ = f^2*(8*q)^6; ring

end
end RHTower
