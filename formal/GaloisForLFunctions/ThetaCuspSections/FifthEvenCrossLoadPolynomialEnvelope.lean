import GaloisForLFunctions.ThetaCuspSections.FifthEvenNativeRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCrossLoadContinuation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspScaleSevenCompensationSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleLikelihoodBounds

/-!
# A quartic lower envelope for theta compensation

An affine tangent bounds the center in terms of the reflection scale.
The exact first-atom slope and uniform mass and derivative errors then
bound the complete compensation. Its slope denominator cancels against
the squared mass, leaving a rational quartic in the scale.
-/

noncomputable section
open Matrix RHTower
namespace GaloisForLFunctions.ThetaCuspSections.FifthCrossEnvelope
open FifthNativeRay FifthRemainder FifthLeadingPair EvenFiveEndpoint

/-- The normalized compensation envelope obtained from the scale-seven tangent. -/
def compensationPolynomial (q : ℝ) : ℝ :=
  3*(2*q-3)^2-(1000001/1000000)*(q/7-99/500)*
    ((2*q-3)*(8*q^2-30*q+15)/2+(2*q-3)^2/100000)

private def firstSlope (q : ℝ) : ℝ := (8*q^2-30*q+15)/(2*(2*q-3))

private theorem firstSlope_pos {q : ℝ} (hq : 7 ≤ q) : 0 < firstSlope q := by
  apply div_pos
  · nlinarith only [hq,sq_nonneg (q-7)]
  · linarith only [hq]

private theorem first_derivative {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      -firstSlope (thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspSourceTerm x 1 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hd := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
  rw [iteratedDeriv_one] at hd
  have hj : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      Real.exp (x/2-q)*(-8*q^3+30*q^2-15*q) := by
    rw [hd]
    dsimp only [thetaCuspGaussianScaleJet,thetaCuspGaussianScaleMoment,q]
    norm_num only [Nat.cast_ofNat,Nat.reduceAdd,pow_one]
    ring
  rw [hj,thetaCuspSourceTerm_one_eq_scale_profile]
  change Real.exp (x/2-q)*(-8*q^3+30*q^2-15*q) =
    -firstSlope q*(Real.exp (x/2-q)*(4*q^2-6*q))
  have hden : 2*q-3 ≠ 0 := by dsimp only [q]; linarith only [hq]
  unfold firstSlope
  field_simp [hden]
  ring

/-- A tangent at a rational upper bound for the scale-seven center. -/
theorem center_tangent {x : ℝ} (hx : 0 ≤ x) :
    2*x ≤ thetaCuspSingleAtomReflectionScale 1 x/7-99/500 := by
  have h := Real.sum_le_exp_of_nonneg (x := (401/500 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have he : (2229/1000 : ℝ) ≤ Real.exp (401/500) := by linarith only [h]
  have hpi : (31415/10000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d4]
  have hp := mul_le_mul hpi he (by norm_num : (0 : ℝ) ≤ 2229/1000) Real.pi_pos.le
  have hbase : (7 : ℝ) ≤ Real.pi*Real.exp (401/500) := by nlinarith only [hp]
  have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2*x-401/500))
    (show 0 ≤ Real.pi*Real.exp (401/500) by positivity)
  have hs := mul_le_mul_of_nonneg_right hbase
    (show 0 ≤ 1+(2*x-401/500) by linarith only [hx])
  simp only [mul_assoc] at ht
  rw [← Real.exp_add,show (401/500 : ℝ)+(2*x-401/500)=2*x by ring] at ht
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one]
  nlinarith only [ht,hs]

private theorem mass_slope_bounds {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x ∧
    thetaCuspFullSource x ≤ (1000001/1000000)*thetaCuspSourceTerm x 1 ∧
    -(firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+1/100000)*
      thetaCuspSourceTerm x 1 ≤ deriv thetaCuspFullSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith only [hq])
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have hε0 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by norm_num) hq
  have hε1 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 1) (by norm_num) hq
  simp only [pow_zero,one_mul] at hε0
  simp only [pow_one] at hε1
  have h0 := abs_thetaCuspFullSource_derivative_sub_first_le_effective 0 hx
    (by norm_num; linarith only [hq])
  have h1 := abs_thetaCuspFullSource_derivative_sub_first_le_effective 1 hx
    (by norm_num; linarith only [hq])
  simp only [iteratedDeriv_zero,pow_zero,mul_one] at h0
  simp only [iteratedDeriv_one,pow_one,first_derivative hq] at h1
  have hsmall0 : 3*regimeOneLikelihoodScale x ≤ (1/1000000 : ℝ) := by
    linarith only [hε0]
  have hsmall1 : 36*q*regimeOneLikelihoodScale x ≤ (1/100000 : ℝ) := by
    change q*regimeOneLikelihoodScale x ≤ 7*(32/1300000000) at hε1
    linarith only [hε1]
  have hm0 := mul_le_mul_of_nonneg_right hsmall0 hf.le
  have hm1 := mul_le_mul_of_nonneg_right hsmall1 hf.le
  refine ⟨(thetaCuspFullSource_mass_bounds_middle (by linarith only [hq])).1,?_,?_⟩
  · have hu := (abs_le.mp h0).2
    change thetaCuspFullSource x-f ≤ 3*regimeOneLikelihoodScale x*f at hu
    change thetaCuspFullSource x ≤ (1000001/1000000)*f
    linarith only [hu,hm0]
  · have hl := (abs_le.mp h1).1
    change -(3*(12*q)*regimeOneLikelihoodScale x*f) ≤
      deriv thetaCuspFullSource x-(-firstSlope q*f) at hl
    change -(firstSlope q+1/100000)*f ≤ _
    nlinarith only [hl,hm1]

private theorem first_mass_square (x : ℝ) :
    thetaCuspSourceTerm x 1^2 =
      sourceUnit x*(2*thetaCuspSingleAtomReflectionScale 1 x-3)^2 := by
  rw [thetaCuspSourceTerm_one_eq_scale_profile]
  unfold sourceUnit
  rw [mul_pow,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show 2*(x/2-thetaCuspSingleAtomReflectionScale 1 x)=
    x-2*thetaCuspSingleAtomReflectionScale 1 x by ring]
  ring

/-- The complete compensation is bounded below by a rational quartic on the scale-seven ray. -/
theorem compensation_polynomial_lower {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    compensationPolynomial (thetaCuspSingleAtomReflectionScale 1 x) ≤
      thetaCuspCenterCompensationSource x/sourceUnit x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let S := firstSlope q+1/100000
  let T := q/7-99/500
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith only [hq])
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hS : 0 < S := by dsimp only [S]; linarith only [firstSlope_pos hq]
  have hb := mass_slope_bounds hq
  change f ≤ F ∧ F ≤ (1000001/1000000)*f ∧ -S*f ≤ deriv thetaCuspFullSource x at hb
  have hsq := mul_self_le_mul_self hf.le hb.1
  have hFf := mul_le_mul_of_nonneg_right hb.2.1 hf.le
  have ht := mul_le_mul_of_nonneg_right (center_tangent hx.le) (sq_nonneg f)
  have hpay1 := mul_le_mul_of_nonneg_left hFf (show 0 ≤ 2*x*S by positivity)
  have hpay2 := mul_le_mul_of_nonneg_right ht
    (show 0 ≤ (1000001/1000000 : ℝ)*S by positivity)
  have hpayment : 2*x*F*S*f ≤ (1000001/1000000)*T*S*f^2 := by
    dsimp only [T]
    nlinarith only [hpay1,hpay2]
  have hd := mul_le_mul_of_nonneg_left hb.2.2 (show 0 ≤ 2*x*F by positivity)
  have hraw : (3-(1000001/1000000)*T*S)*f^2 ≤ thetaCuspCenterCompensationSource x := by
    change (3-(1000001/1000000)*T*S)*f^2 ≤ 3*F^2+2*x*F*deriv thetaCuspFullSource x
    nlinarith only [hsq,hpayment,hd]
  have hden : 2*q-3 ≠ 0 := by dsimp only [q]; linarith only [hq]
  have he : compensationPolynomial q=(3-(1000001/1000000)*T*S)*(2*q-3)^2 := by
    dsimp only [compensationPolynomial,T,S,firstSlope]
    field_simp [hden]
  have hK := sourceUnit_pos (show 5 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith only [hq])
  apply (le_div_iff₀ hK).mpr
  change compensationPolynomial q*sourceUnit x ≤ _
  calc
    _ = (3-(1000001/1000000)*T*S)*f^2 := by
      rw [he]
      dsimp only [f,q]
      rw [first_mass_square]
      ring
    _ ≤ _ := hraw

/-- A rational inverse-power envelope for the unequal leading-pair weight. -/
theorem cross_weight_upper {q : ℝ} (hq : 7 ≤ q) :
    Real.exp (-3*q) ≤ ((19/25000000000 : ℝ)*7^15)/q^15 := by
  have hq0 : 0 < q := by linarith only [hq]
  have hp := pow_mul_exp_neg_le_stationary_radius 15
    (a := 7) (t := q) (by norm_num) hq0.le
  simp only [Nat.cast_ofNat] at hp
  have he : Real.exp (-(6/7*q)) ≤ Real.exp (-6 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith only [hq])
  have hm := mul_le_mul hp he (Real.exp_pos _).le
    (show 0 ≤ (7 : ℝ)^15*Real.exp (-15) by positivity)
  have hl : (q^15*Real.exp (-(15/7*q)))*Real.exp (-(6/7*q)) =
      q^15*Real.exp (-3*q) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hr : ((7 : ℝ)^15*Real.exp (-15))*Real.exp (-6) =
      (7 : ℝ)^15*Real.exp (-21) := by
    rw [mul_assoc,← Real.exp_add]
    norm_num
  rw [hl,hr] at hm
  have h21 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 21
  rw [← Real.exp_nat_mul] at h21
  simp only [Nat.cast_ofNat,mul_one] at h21
  have hb : (25000000000/19 : ℝ) ≤ Real.exp 21 :=
    (by norm_num : (25000000000/19 : ℝ) ≤ (2.7182818283 : ℝ)^21).trans h21
  have hd : Real.exp (-21 : ℝ) ≤ 19/25000000000 := by
    rw [Real.exp_neg,inv_eq_one_div]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 25000000000/19) hb
    norm_num at h
    simpa only [one_div] using h
  have hs := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 7^15 by positivity)
  apply (le_div_iff₀ (pow_pos hq0 15)).mpr
  nlinarith only [hm,hs]

/-- The fixed cross-load in normalized Gaussian coordinates. -/
def crossLoadGram (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (loadMap*nativeBasis q)ᴴ*paidSevenSchur*(loadMap*nativeBasis q)

/-- A rational matrix lower model, affine in the unequal-pair weight. -/
def crossModel (q z : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram (leadingMatrix q z)+compensationPolynomial q • crossLoadGram q-
    (147/4000 : ℝ) • 1

private theorem normalized_cross_decomposition (x : ℝ) :
    normalizedGram x (crossRepair x) = sourceGram x+
      (thetaCuspCenterCompensationSource x/sourceUnit x) •
        crossLoadGram (thetaCuspSingleAtomReflectionScale 1 x) := by
  simp only [sourceGram,crossRepair,normalizedGram_eq_congruence,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,smul_add,smul_smul,
    crossLoadGram,crossLoad,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [show (1/sourceUnit x)*thetaCuspCenterCompensationSource x=
    thetaCuspCenterCompensationSource x/sourceUnit x by ring]

/-- The complete fixed cross-load dominates the rational leading-pair model on the scale-seven ray. -/
theorem cross_model_lower {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (crossModel (thetaCuspSingleAtomReflectionScale 1 x)
      (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) *ᵥ v) ≤
      v ⬝ᵥ (normalizedGram x (crossRepair x) *ᵥ v) := by
  have hl := sourceGram_retained_lower
    (show 5 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith only [hq]) v
  have hV := (crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same
    (loadMap*nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hV
  change 0 ≤ v ⬝ᵥ (crossLoadGram (thetaCuspSingleAtomReflectionScale 1 x) *ᵥ v) at hV
  have hc := mul_le_mul_of_nonneg_right (compensation_polynomial_lower hq) hV
  rw [normalized_cross_decomposition]
  simp only [crossModel,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,
    Matrix.one_mulVec,dotProduct_add,dotProduct_sub,dotProduct_smul,smul_eq_mul]
  have he : v ⬝ᵥ v=∑ i, v i^2 := by simp only [dotProduct,pow_two]
  rw [he]
  linarith only [hl,hc]

end GaloisForLFunctions.ThetaCuspSections.FifthCrossEnvelope
