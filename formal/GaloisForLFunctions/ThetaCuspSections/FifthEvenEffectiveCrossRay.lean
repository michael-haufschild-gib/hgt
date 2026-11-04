import GaloisForLFunctions.ThetaCuspSections.FifthEvenNativeRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCrossLoadContinuation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspScaleSevenCompensationSource

/-!
# An effective ray for the fifth theta cross-load

The native Gaussian reserve grows quadratically in the reflection scale.
The two load rows decay with powers two and three. The complete compensation
therefore has a uniformly bounded adverse contribution after normalization.
-/

noncomputable section
open Matrix RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.FifthEffectiveCrossRay
open FifthNativeRay FifthLeadingPair FifthRemainder EvenFiveEndpoint

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

local macro "norm_endpoint" : tactic =>
  `(tactic| norm_num [loss,EvenFiveBoundary.scaleSevenCompensationLoss,Fin.sum_univ_succ,gap,schur2,kernelNum,
    crossZero,crossOne,schur3,headDet,adj,mOrigin,EvenFiveOrigin.originMomentPolynomial,
    mSeven,retainedRatio,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
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
    radialCoeffs_6_13,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,
    radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,
    radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,
    radialCoeffs_7_14,radialCoeffs_7_15,radial_eight_coeff,radial_seven_zero_16,
    radial_seven_zero_17,radial_seven_zero_18,radial_seven_zero_19,radialStepCoeff,
    radialInnerCoeff])


private theorem coefficient_first_le : paidSevenSchur 0 0 ≤ 50000000 := by
  simp only [paidSevenSchur]
  norm_endpoint

private theorem coefficient_second_le : paidSevenSchur 1 1 ≤ 10000000000000 := by
  simp only [paidSevenSchur]
  norm_endpoint

/-- The two load rows after removing their respective scale powers. -/
def scaledLoadRows (q : ℝ) : Matrix (Fin 2) (Fin 5) ℝ :=
  !![0,0,1/256,(35/q-10)/1024,35*(1-7/q)/2048;
     0,0,0,1/12288,-7*(1-7/q)/24576]

private theorem scaledLoadRows_eq {q : ℝ} (hq : q ≠ 0) (i : Fin 2) (j : Fin 5) :
    scaledLoadRows q i j = q^(2+i.val)*(loadMap*nativeBasis q) i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [scaledLoadRows,loadMap,nativeBasis,gaussianBasis,Matrix.mul_apply,
      Fin.sum_univ_succ]
  all_goals field_simp [hq] <;> ring

private theorem row_norm_bounds {q : ℝ} (hq : 7 ≤ q) :
    (∑ j, (scaledLoadRows q 0 j)^2) ≤ (1/2000 : ℝ) ∧
    (∑ j, (scaledLoadRows q 1 j)^2) ≤ (1/10000000 : ℝ) := by
  have hq0 : 0 < q := by linarith only [hq]
  have hi : 0 ≤ 7/q := div_nonneg (by norm_num) hq0.le
  have hu : 7/q ≤ 1 := (div_le_one hq0).mpr hq
  have h7 : (1-7/q)^2 ≤ 1 := by nlinarith only [hi,hu,mul_nonneg hi (sub_nonneg.mpr hu)]
  have h35 : (35/q-10)^2 ≤ 100 := by
    have he : 35/q=5*(7/q) := by ring
    rw [he]
    nlinarith only [hi,hu,mul_nonneg hi (sub_nonneg.mpr hu)]
  norm_num [scaledLoadRows,Fin.sum_univ_succ]
  constructor <;> nlinarith only [h7,h35]

private theorem coefficient_energy_le (v : Fin 2 → ℝ) :
    v ⬝ᵥ (paidSevenSchur *ᵥ v) ≤
      100000000*(v 0)^2+20000000000000*(v 1)^2 := by
  have h := crossCoefficient_posDef.posSemidef.dotProduct_mulVec_nonneg ![v 0,-v 1]
  have hs : paidSevenSchur 1 0=paidSevenSchur 0 1 := by
    have hh := congrFun (congrFun paidSevenSchur_hermitian 0) 1
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hh
  have h0 := mul_le_mul_of_nonneg_right coefficient_first_le (sq_nonneg (v 0))
  have h1 := mul_le_mul_of_nonneg_right coefficient_second_le (sq_nonneg (v 1))
  norm_num [dotProduct,Matrix.mulVec,Fin.sum_univ_two,hs] at h ⊢
  nlinarith only [h,h0,h1]

private def loadGram (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (loadMap*nativeBasis q)ᴴ*paidSevenSchur*(loadMap*nativeBasis q)

private theorem loadGram_energy (q : ℝ) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (loadGram q *ᵥ v) =
      ((loadMap*nativeBasis q)*ᵥv) ⬝ᵥ
        (paidSevenSchur*ᵥ((loadMap*nativeBasis q)*ᵥv)) := by
  simp only [loadGram,Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose,star_trivial]

private theorem scaledLoadRows_mulVec {q : ℝ} (hq : q ≠ 0)
    (v : Fin 5 → ℝ) (i : Fin 2) :
    (scaledLoadRows q *ᵥ v) i = q^(2+i.val)*((loadMap*nativeBasis q)*ᵥv) i := by
  simp only [Matrix.mulVec,dotProduct,scaledLoadRows_eq hq,Finset.mul_sum,mul_assoc]

private theorem loadGram_energy_bound {q : ℝ} (hq : 5000 ≤ q) (v : Fin 5 → ℝ) :
    q^4*(v ⬝ᵥ (loadGram q *ᵥ v)) ≤ 50002*(∑ i, v i^2) := by
  let w := (loadMap*nativeBasis q)*ᵥv
  have hq0 : 0 < q := by linarith only [hq]
  have hn := row_norm_bounds (show 7 ≤ q by linarith only [hq])
  have hS : 0 ≤ ∑ i, v i^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc (i : Fin 2) := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (scaledLoadRows q i) v
  have h0 := hc 0
  have h1 := hc 1
  change ((scaledLoadRows q*ᵥv) 0)^2 ≤ _ at h0
  change ((scaledLoadRows q*ᵥv) 1)^2 ≤ _ at h1
  rw [scaledLoadRows_mulVec hq0.ne'] at h0 h1
  norm_num only [Fin.val_zero,Fin.val_one,Nat.reduceAdd,mul_pow] at h0 h1
  have hr0 := mul_le_mul_of_nonneg_right hn.1 hS
  have hr1 := mul_le_mul_of_nonneg_right hn.2 hS
  have ha : q^4*(w 0)^2 ≤ (1/2000)*(∑ i, v i^2) := by
    dsimp only [w]
    nlinarith only [h0,hr0]
  have hb : q^6*(w 1)^2 ≤ (1/10000000)*(∑ i, v i^2) := by
    dsimp only [w]
    nlinarith only [h1,hr1]
  have hq2 : 1000000 ≤ q^2 := by nlinarith only [hq,sq_nonneg (q-5000)]
  have hm := mul_le_mul_of_nonneg_right hq2
    (show 0 ≤ q^4*(w 1)^2 by positivity)
  have hb' : q^4*(w 1)^2 ≤ (1/10000000000000)*(∑ i, v i^2) := by
    nlinarith only [hm,hb]
  have he := mul_le_mul_of_nonneg_left (coefficient_energy_le w)
    (show 0 ≤ q^4 by positivity)
  rw [loadGram_energy]
  change q^4*(w ⬝ᵥ (paidSevenSchur *ᵥ w)) ≤ _
  nlinarith only [he,ha,hb']

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

/-- The adverse compensation has a polynomial bound in the first-pair normalization. -/
theorem compensation_lower {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -(26/25 : ℝ)*thetaCuspSingleAtomReflectionScale 1 x^4 ≤
      thetaCuspCenterCompensationSource x/sourceUnit x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let d := deriv thetaCuspFullSource x
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith only [hq])
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hqp : 0 < q := by dsimp only [q]; linarith only [hq]
  have hb := thetaCuspFullSource_mass_slope_le_scaleSeven hq
  change F ≤ (101/100)*f ∧ |d| ≤ (201/100)*q*f at hb
  have hprod := mul_le_mul hb.1 hb.2 (abs_nonneg d) (by positivity : (0 : ℝ) ≤ (101/100)*f)
  have hprod1 : F*|d| ≤ (52/25)*q*f^2 := by
    have hpos : 0 ≤ q*f^2 := by positivity
    nlinarith only [hprod,hpos]
  have hprod2 := mul_le_mul_of_nonneg_left hprod1 (by positivity : (0 : ℝ) ≤ 2*x)
  have hxd := sixteen_mul_center_le_firstAtomScale hx.le
  change 16*x ≤ q at hxd
  have hscale := mul_le_mul_of_nonneg_right hxd (by positivity : (0 : ℝ) ≤ (13/50)*q*f^2)
  have hneg := mul_le_mul_of_nonneg_left (neg_abs_le d) (by positivity : (0 : ℝ) ≤ 2*x*F)
  have hraw : -(13/50)*q^2*f^2 ≤ thetaCuspCenterCompensationSource x := by
    change -(13/50)*q^2*f^2 ≤ 3*F^2+2*x*F*d
    nlinarith only [hprod2,hscale,hneg,sq_nonneg F]
  have hK := sourceUnit_pos (show 5 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith only [hq])
  have hs : (2*q-3)^2 ≤ 4*q^2 := by nlinarith only [hq]
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (13/50)*q^2*sourceUnit x by positivity)
  have he : f^2=sourceUnit x*(2*q-3)^2 := first_mass_square x
  rw [he] at hraw
  apply (le_div_iff₀ hK).mpr
  change (-(26/25)*q^4)*sourceUnit x ≤ _
  nlinarith only [hraw,hm]

/-- The fixed cross-loaded source in normalized Gaussian coordinates. -/
def crossGram (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := normalizedGram x (crossRepair x)

private theorem crossGram_decomposition (x : ℝ) :
    crossGram x = sourceGram x+
      (thetaCuspCenterCompensationSource x/sourceUnit x) •
        loadGram (thetaCuspSingleAtomReflectionScale 1 x) := by
  simp only [crossGram,sourceGram,crossRepair,normalizedGram_eq_congruence,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,smul_add,smul_smul,
    loadGram,crossLoad,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [show (1/sourceUnit x)*thetaCuspCenterCompensationSource x=
    thetaCuspCenterCompensationSource x/sourceUnit x by ring]

/-- An explicit quadratic reserve for the complete fixed cross-load on a concrete source ray. -/
theorem crossGram_coercive {x : ℝ}
    (hq : 5000 ≤ thetaCuspSingleAtomReflectionScale 1 x) (v : Fin 5 → ℝ) :
    20000*(∑ i, v i^2) ≤ v ⬝ᵥ (crossGram x *ᵥ v) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq5 : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hq7 : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hS : 0 ≤ ∑ i, v i^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hl := sourceGram_growing_coercive hq5 v
  have hf : (75000 : ℝ) ≤ (2*q-3)^2/1000-147/4000 := by
    nlinarith only [hq,sq_nonneg (q-5000)]
  have hfloor := mul_le_mul_of_nonneg_right hf hS
  have hload := (crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same
    (loadMap*nativeBasis q)).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hload
  change 0 ≤ v ⬝ᵥ (loadGram q *ᵥ v) at hload
  have hg := mul_le_mul_of_nonneg_right (compensation_lower hq7) hload
  have hc := loadGram_energy_bound hq v
  rw [crossGram_decomposition]
  simp only [Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  nlinarith only [hl,hfloor,hg,hc,hS]

/-- The normalized fixed cross-load is strictly positive at every scale at least five thousand. -/
theorem crossGram_posDef {x : ℝ}
    (hq : 5000 ≤ thetaCuspSingleAtomReflectionScale 1 x) : (crossGram x).PosDef := by
  have hn := sourceGram_posDef
    (show 5 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith only [hq])
  have hL := crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same
    (loadMap*nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))
  have hh : (crossGram x).IsHermitian := by
    rw [crossGram_decomposition]
    exact hn.isHermitian.add (hL.isHermitian.smul (by rfl))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hh fun v hv => ?_
  have hS : 0 < ∑ i, v i^2 := by
    obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i,Finset.mem_univ i,sq_pos_of_ne_zero hi⟩
  simpa only [star_trivial] using
    (mul_pos (by norm_num : (0 : ℝ) < 20000) hS).trans_le (crossGram_coercive hq v)

/-- The endpoint-compatible cross-load has an explicit effective positive source ray. -/
theorem crossRepair_posDef_of_scale_ge_fiveThousand {x : ℝ}
    (hq : 5000 ≤ thetaCuspSingleAtomReflectionScale 1 x) : (crossRepair x).PosDef := by
  let B := nativeBasis (thetaCuspSingleAtomReflectionScale 1 x)
  have hK := sourceUnit_pos
    (show 5 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith only [hq])
  have hgram := (crossGram_posDef hq).smul hK
  have he : sourceUnit x • crossGram x=Bᴴ*crossRepair x*B := by
    rw [crossGram,normalizedGram_eq_congruence,smul_smul]
    rw [show sourceUnit x*(1/sourceUnit x)=1 by field_simp [hK.ne']]
    exact one_smul _ _
  rw [he] at hgram
  have hB : B.det ≠ 0 := (nativeBasis_det_pos
    (show 0 < thetaCuspSingleAtomReflectionScale 1 x by linarith only [hq])).ne'
  have hbinv : B*B⁻¹=1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB)
  have hinj : Function.Injective (B⁻¹).mulVec := by
    intro v w h
    have hh := congrArg (fun u => B*ᵥu) h
    simpa only [Matrix.mulVec_mulVec,hbinv,Matrix.one_mulVec] using hh
  have hback := hgram.conjTranspose_mul_mul_same hinj
  have hb : (B⁻¹)ᴴ*(Bᴴ*crossRepair x*B)*B⁻¹=crossRepair x := by
    calc
      _ = (B*B⁻¹)ᴴ*crossRepair x*(B*B⁻¹) := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [hbinv]; simp
  rwa [hb] at hback

/-- The fixed cross-load is positive beyond the explicit center four. -/
theorem crossRepair_posDef_of_four_le {x : ℝ} (hx : 4 ≤ x) : (crossRepair x).PosDef := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718/1000)
    (show (2718/1000 : ℝ) ≤ Real.exp 1 by linarith only [Real.exp_one_gt_d9]) 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have he : (5000/3 : ℝ) ≤ Real.exp (2*x) :=
    (show (5000/3 : ℝ) ≤ Real.exp 8 by linarith only [hp]).trans
      (Real.exp_le_exp.mpr (by linarith only [hx]))
  have hq := mul_le_mul Real.pi_gt_three.le he (by norm_num : (0 : ℝ) ≤ 5000/3)
    Real.pi_pos.le
  norm_num at hq
  apply crossRepair_posDef_of_scale_ge_fiveThousand
  simpa only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one] using hq

end GaloisForLFunctions.ThetaCuspSections.FifthEffectiveCrossRay
