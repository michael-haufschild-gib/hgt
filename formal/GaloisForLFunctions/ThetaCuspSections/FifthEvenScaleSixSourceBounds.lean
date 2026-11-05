import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleSixData
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossCompactEnvelope
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTruncatedQuarticFlux

/-!
# Complete-source obstruction at theta scale six

The complete fifth even source is compared with a rational leading-pair
matrix, including all omitted pure atoms and the infinite theta tail.
Every normalized cross-load at most `−100` has a negative direction.
The quartic load and its literal derivative at every critical aperture
cross this boundary inside the truncation support.
-/

noncomputable section
open Matrix RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.SixSourceBounds
open FifthNativeRay FifthLeadingPair FifthRemainder EightCrossData
open scoped EightCrossData

/-- The center at which the first reflected atom has scale six. -/
def center : ℝ := Real.log (6/Real.pi)/2

theorem center_scale : thetaCuspSingleAtomReflectionScale 1 center=6 := by
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one,center]
  rw [show 2*(Real.log (6/Real.pi)/2)=Real.log (6/Real.pi) by ring,
    Real.exp_log (div_pos (by norm_num) Real.pi_pos)]
  field_simp [Real.pi_pos.ne']

private def weight : ℝ := 1522998/100000000000000

private theorem decay_bounds :
    (15229979/1000000000000000 : ℝ) ≤ Real.exp (-18) ∧ Real.exp (-18) ≤ weight := by
  have hlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 18
  have hhi := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 18
  rw [← Real.exp_nat_mul] at hlo hhi
  simp only [Nat.cast_ofNat,mul_one] at hlo hhi
  have hl : (100000000000000/1522998 : ℝ) ≤ Real.exp 18 :=
    (by norm_num : (100000000000000/1522998 : ℝ) ≤ (2.7182818283 : ℝ)^18).trans hlo
  have hu : Real.exp 18 ≤ (1000000000000000/15229979 : ℝ) :=
    hhi.trans (by norm_num : (2.7182818286 : ℝ)^18 ≤ 1000000000000000/15229979)
  rw [Real.exp_neg,inv_eq_one_div]
  constructor
  · have h := one_div_le_one_div_of_le (Real.exp_pos 18) hu
    norm_num at h
    simpa only [one_div] using h
  · have h := one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 100000000000000/1522998) hl
    norm_num [weight] at h ⊢
    exact h

private def mixedSix : Matrix (Fin 5) (Fin 5) ℝ :=
  polyModel 6 1 0 0-polyModel 6 0 0 0
private def pureSix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianEntry (fun k => rMoment q k/6^k)

private theorem mixed_bound_0 (j : Fin 5) : |(mixedSix) 0 j| ≤ 1000000000000 := by
  fin_cases j <;> simp only [mixedSix,Matrix.sub_apply]
  all_goals norm_cross_model

private theorem mixed_bound_1 (j : Fin 5) : |(mixedSix) 1 j| ≤ 1000000000000 := by
  fin_cases j <;> simp only [mixedSix,Matrix.sub_apply]
  all_goals norm_cross_model

private theorem mixed_bound_2 (j : Fin 5) : |(mixedSix) 2 j| ≤ 1000000000000 := by
  fin_cases j <;> simp only [mixedSix,Matrix.sub_apply]
  all_goals norm_cross_model
  all_goals norm_num [Fin.ext_iff]

private theorem mixed_bound_3 (j : Fin 5) : |(mixedSix) 3 j| ≤ 1000000000000 := by
  fin_cases j <;> simp only [mixedSix,Matrix.sub_apply]
  all_goals norm_cross_model
  all_goals norm_num [Fin.ext_iff]

private theorem mixed_bound_4 (j : Fin 5) : |(mixedSix) 4 j| ≤ 1000000000000 := by
  fin_cases j <;> simp only [mixedSix,Matrix.sub_apply]
  all_goals norm_cross_model
  all_goals norm_num [Fin.ext_iff]

private theorem pure_two_bound_0 (j : Fin 5) : |(pureSix 24) 0 j| ≤ 100000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem pure_two_bound_1 (j : Fin 5) : |(pureSix 24) 1 j| ≤ 100000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem pure_two_bound_2 (j : Fin 5) : |(pureSix 24) 2 j| ≤ 100000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem pure_two_bound_3 (j : Fin 5) : |(pureSix 24) 3 j| ≤ 100000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem pure_two_bound_4 (j : Fin 5) : |(pureSix 24) 4 j| ≤ 100000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem pure_three_bound_0 (j : Fin 5) : |(pureSix 54) 0 j| ≤ 100000000000000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem pure_three_bound_1 (j : Fin 5) : |(pureSix 54) 1 j| ≤ 100000000000000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem pure_three_bound_2 (j : Fin 5) : |(pureSix 54) 2 j| ≤ 100000000000000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem pure_three_bound_3 (j : Fin 5) : |(pureSix 54) 3 j| ≤ 100000000000000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem pure_three_bound_4 (j : Fin 5) : |(pureSix 54) 4 j| ≤ 100000000000000000000 := by
  fin_cases j <;> simp only [pureSix,gaussianEntry]
  all_goals norm_cross_model

private theorem mixed_bound (i j : Fin 5) : |(mixedSix) i j| ≤ 1000000000000 := by
  fin_cases i
  · exact mixed_bound_0 j
  · exact mixed_bound_1 j
  · exact mixed_bound_2 j
  · exact mixed_bound_3 j
  · exact mixed_bound_4 j

private theorem pure_two_bound (i j : Fin 5) : |(pureSix 24) i j| ≤ 100000000000 := by
  fin_cases i
  · exact pure_two_bound_0 j
  · exact pure_two_bound_1 j
  · exact pure_two_bound_2 j
  · exact pure_two_bound_3 j
  · exact pure_two_bound_4 j

private theorem pure_three_bound (i j : Fin 5) : |(pureSix 54) i j| ≤ 100000000000000000000 := by
  fin_cases i
  · exact pure_three_bound_0 j
  · exact pure_three_bound_1 j
  · exact pure_three_bound_2 j
  · exact pure_three_bound_3 j
  · exact pure_three_bound_4 j

private theorem pure_source_eq (n : ℕ) :
    FifthNativeRay.pureGram n center =
      ((n : ℝ)^4*Real.exp (-(2*(n : ℝ)^2-2)*6)) • pureSix (6*(n : ℝ)^2) := by
  rw [FifthNativeRay.pureGram,normalizedGram,pureSix,← gaussian_eq,← gaussianGram_smul]
  congr 1
  ext i j
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hj := _root_.RHTower.ThetaCuspOddFourThreeAtom.signed_pair_even n n (i.val+j.val) center
  rw [center_scale] at hj
  have hp :
      (thetaPairRadialEvenPolynomial ((n : ℝ)^2*(n : ℝ)^2*6^2) (i.val+j.val)).eval
        (((n : ℝ)^2+(n : ℝ)^2)*6) = rMoment (6*(n : ℝ)^2) (i.val+j.val) := by
    rw [show (n : ℝ)^2*(n : ℝ)^2*6^2=(6*(n : ℝ)^2)^2 by ring,
      show ((n : ℝ)^2+(n : ℝ)^2)*6=2*(6*(n : ℝ)^2) by ring]
    exact radial_eq (6*(n : ℝ)^2) (i.val+j.val) (by omega)
  rw [hp] at hj
  have he : Real.exp (center-((n : ℝ)^2+(n : ℝ)^2)*6) =
      Real.exp (center-2*6)*Real.exp (-(2*(n : ℝ)^2-2)*6) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hj
  simp only [FifthNativeRay.pureMatrix,center_scale,Matrix.smul_apply,smul_eq_mul]
  rw [hj]
  have hk : sourceUnit center=4*6^2*Real.exp (center-2*6) := by
    simp only [sourceUnit,center_scale]
  rw [hk]
  field_simp [Real.exp_ne_zero]

private theorem pure_two_small (i j : Fin 5) :
    |FifthNativeRay.pureGram 2 center i j| ≤ (1/1000 : ℝ) := by
  have he : Real.exp (-36 : ℝ)=Real.exp (-18 : ℝ)^2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [pure_source_eq]
  norm_num only [Nat.cast_ofNat,show (6 : ℝ)*2^2=24 by norm_num,
    show (2 : ℝ)^4=16 by norm_num,show -(2*(2 : ℝ)^2-2)*6=-36 by norm_num,
    Matrix.smul_apply,smul_eq_mul]
  rw [abs_mul,abs_of_pos (by positivity : (0 : ℝ)<16*Real.exp (-36))]
  have hz := pow_le_pow_left₀ (Real.exp_pos (-18)).le decay_bounds.2 2
  rw [← he] at hz
  calc
    _ ≤ (16*weight^2)*100000000000 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num)) (pure_two_bound i j)
        (abs_nonneg _) (by positivity)
    _ ≤ _ := by norm_num [weight]

private theorem pure_three_small (i j : Fin 5) :
    |FifthNativeRay.pureGram 3 center i j| ≤ (1/1000000 : ℝ) := by
  have he : Real.exp (-72 : ℝ)=Real.exp (-18 : ℝ)^4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hz := pow_le_pow_left₀ (Real.exp_pos (-18)).le decay_bounds.2 4
  rw [← he] at hz
  have hz' : Real.exp (-96 : ℝ) ≤ weight^4 :=
    (Real.exp_le_exp.mpr (by norm_num : (-96 : ℝ) ≤ -72)).trans hz
  rw [pure_source_eq]
  norm_num only [Nat.cast_ofNat,show (6 : ℝ)*3^2=54 by norm_num,
    show (3 : ℝ)^4=81 by norm_num,show -(2*(3 : ℝ)^2-2)*6=-96 by norm_num,
    Matrix.smul_apply,smul_eq_mul]
  rw [abs_mul,abs_of_pos (by positivity : (0 : ℝ)<81*Real.exp (-96))]
  calc
    _ ≤ (81*weight^4)*100000000000000000000 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hz' (by norm_num)) (pure_three_bound i j)
        (abs_nonneg _) (by norm_num [weight])
    _ ≤ _ := by norm_num [weight]

private theorem weight_error : |Real.exp (-18 : ℝ)-weight| ≤ (1/1000000000000000 : ℝ) := by
  rw [abs_of_nonpos (sub_nonpos.mpr decay_bounds.2)]
  have hl := decay_bounds.1
  norm_num [weight] at hl ⊢
  linarith only [hl]

private theorem leading_weight_difference (z w : ℝ) :
    gaussianGram (leadingMatrix 6 z)-gaussianGram (leadingMatrix 6 w) =
      (z-w) • mixedSix := by
  have hm : leadingMatrix 6 z=leadingMatrix 6 w+
      (z-w) • (leadingMatrix 6 1-leadingMatrix 6 0) := by
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      leadingMatrix,leadingMoment]
    ring
  have hB : gaussianGram (leadingMatrix 6 1-leadingMatrix 6 0)=mixedSix := by
    unfold mixedSix
    rw [polyModel_eq (by norm_num : (6 : ℝ) ≠ 0),polyModel_eq (by norm_num : (6 : ℝ) ≠ 0)]
    simp only [zero_smul,add_zero]
    ext i j
    simp only [gaussianGram,Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib]
  rw [hm,gaussianGram_add,gaussianGram_smul,hB]
  abel

private theorem leading_error (i j : Fin 5) :
    |(gaussianGram (leadingMatrix 6 (Real.exp (-18)))-
      gaussianGram (leadingMatrix 6 weight)) i j| ≤ (1/1000 : ℝ) := by
  rw [leading_weight_difference]
  simp only [Matrix.smul_apply,smul_eq_mul,abs_mul]
  have h := mul_le_mul weight_error (mixed_bound i j) (abs_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1/1000000000000000)
  norm_num at h
  exact h

private theorem source_error_entry (i j : Fin 5) :
    |(sourceGram center-gaussianGram (leadingMatrix 6 weight)) i j| ≤ (1/100 : ℝ) := by
  have hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 center := by rw [center_scale]; norm_num
  have hd := sourceGram_decomposition hq
  rw [center_scale] at hd
  norm_num only [show (-3 : ℝ)*6=-18 by norm_num] at hd
  have hr := remainderGram_bound hq i j
  have hp2 := pure_two_small i j
  have hp3 := pure_three_small i j
  have he := leading_error i j
  have hid : (sourceGram center-gaussianGram (leadingMatrix 6 weight)) i j =
      ((gaussianGram (leadingMatrix 6 (Real.exp (-18)))-gaussianGram (leadingMatrix 6 weight)) i j+
        remainderGram center i j)+FifthNativeRay.pureGram 2 center i j+FifthNativeRay.pureGram 3 center i j := by
    rw [hd]
    simp only [Matrix.add_apply,Matrix.sub_apply]
    ring
  rw [hid]
  calc
    _ ≤ |(gaussianGram (leadingMatrix 6 (Real.exp (-18)))-gaussianGram (leadingMatrix 6 weight)) i j|+
        |remainderGram center i j|+|FifthNativeRay.pureGram 2 center i j|+
        |FifthNativeRay.pureGram 3 center i j| := by
      have ht (a b c d : ℝ) : |a+b+c+d| ≤ |a|+|b|+|c|+|d| := by
        have h1 := abs_add_le a b
        have h2 := abs_add_le (a+b) c
        have h3 := abs_add_le (a+b+c) d
        linarith only [h1,h2,h3]
      exact ht _ _ _ _
    _ ≤ ((1/1000 : ℝ)+147/20000)+1/1000+1/1000000 :=
      add_le_add (add_le_add (add_le_add he hr) hp2) hp3
    _ ≤ _ := by norm_num

/-- At scale six the complete source differs from the retained rational form by at most one twentieth. -/
theorem source_error (v : Fin 5 → ℝ) :
    |v ⬝ᵥ (sourceGram center *ᵥ v)-v ⬝ᵥ (gaussianGram (leadingMatrix 6 weight) *ᵥ v)| ≤
      (1/20 : ℝ)*(∑ i, v i^2) := by
  have h := _root_.RHTower.abs_dotProduct_mulVec_le
    (sourceGram center-gaussianGram (leadingMatrix 6 weight)) (by norm_num : (0 : ℝ) ≤ 1/100)
    source_error_entry v
  norm_num only [Matrix.sub_mulVec,dotProduct_sub,Fintype.card_fin,Nat.cast_ofNat] at h
  simpa only [show (5 : ℝ)*(1/100)=1/20 by norm_num] using h

theorem center_pos : 0 < center :=
  regimeOne_pos_of_six_le (by rw [center_scale])

private theorem center_le_third : center ≤ (1/3 : ℝ) := by
  have h := FifthCrossEnvelope.center_tangent center_pos.le
  rw [center_scale] at h
  linarith only [h]

private theorem full_mass_square_upper : thetaCuspFullSource center^2 ≤ 83*sourceUnit center := by
  have hm := (thetaCuspFullSource_mass_bounds_middle
    (show 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 center by rw [center_scale]; norm_num)).2
  have hs := mul_self_le_mul_self (thetaCuspFullSource_pos_all center).le hm
  have hf := FifthCrossEnvelope.first_mass_square center
  rw [center_scale] at hf
  norm_num only [show (2*(6 : ℝ)-3)^2=81 by norm_num] at hf
  have hK := (sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)).le
  nlinarith only [hs,hf,hK]

private theorem critical_hyperbolic_remainder {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/3) :
    u*Real.cosh u-Real.sinh u ≤ (1/17)*Real.sinh u := by
  have hc0 := HTGeometry.cosh_sub_one_le hu
  have hsq := mul_self_le_mul_self hu hu1
  have hm := mul_le_mul_of_nonneg_right hsq (Real.cosh_pos u).le
  have hc : Real.cosh u ≤ 18/17 := by nlinarith only [hc0,hm]
  have hp := mul_le_mul_of_nonneg_left hc hu
  have hs := HTGeometry.self_le_sinh_of_nonneg hu
  linarith only [hp,hs]

/-- Every critical aperture retains a negative quartic load of at least one hundred twenty source units. -/
theorem weighted_derivative_upper {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) :
    deriv (FifthPolynomialCross.flux a) (2*center) ≤
      (2*center*Real.sinh (a*(2*center)))*(-120*sourceUnit center) := by
  have hr : 0 ≤ 2*center := mul_nonneg (by norm_num) center_pos.le
  have hr1 : 2*center ≤ 1 := by linarith only [center_le_third]
  have hu : 0 ≤ a*(2*center) := mul_nonneg ha0 hr
  have hu1 : a*(2*center) ≤ 1/3 := by
    have h := mul_le_mul_of_nonneg_right ha.le hr
    nlinarith only [h,center_le_third]
  have hs : 0 ≤ Real.sinh (a*(2*center)) := Real.sinh_nonneg_iff.mpr hu
  have hp : FifthPolynomialCross.profile (2*center) ≤ 1 := by
    have ht := mul_self_le_mul_self hr hr1
    have hp0 : 0 ≤ 1-(2*center)^2/2 := by nlinarith only [ht]
    have hp1 : 1-(2*center)^2/2 ≤ 1 := by nlinarith only [sq_nonneg (2*center)]
    have h := mul_self_le_mul_self hp0 hp1
    dsimp only [FifthPolynomialCross.profile]
    nlinarith only [h]
  have hw : 0 ≤ 2*center*Real.sinh (a*(2*center)) := mul_nonneg hr hs
  have hrem := mul_le_mul_of_nonneg_left (critical_hyperbolic_remainder hu hu1)
    (show 0 ≤ FifthPolynomialCross.profile (2*center)*(2*center)*thetaCuspFullSource center^2 from
      mul_nonneg (mul_nonneg (FifthPolynomialCross.profile_nonneg _) hr) (sq_nonneg _))
  have hprof := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ (2*center)*Real.sinh (a*(2*center))*thetaCuspFullSource center^2/17 by positivity)
  have hmass := mul_le_mul_of_nonneg_left full_mass_square_upper
    (show 0 ≤ (2*center)*Real.sinh (a*(2*center))/17 by positivity)
  have hmain := mul_le_mul_of_nonneg_left
    (FifthPolynomialCross.compensation_six_upper center_scale) hw
  have hK := (sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)).le
  have hbudget := mul_nonneg hw hK
  rw [FifthPolynomialCross.deriv_flux_remainder,show 2*center/2=center by ring]
  nlinarith only [hrem,hprof,hmass,hmain,hbudget]

/-- The complete native source with an arbitrary scalar cross-load at scale six. -/
def loadedSource (c : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeShiftedMatrix 5 0 center+c • EvenFiveEndpoint.crossLoad EvenFiveEndpoint.paidSevenSchur

private theorem normalized_loaded (c : ℝ) :
    normalizedGram center (loadedSource c)=sourceGram center+(c/sourceUnit center) • loadGram 6 := by
  simp only [loadedSource,sourceGram,normalizedGram_eq_congruence,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,smul_add,smul_smul,
    loadGram,EvenFiveEndpoint.crossLoad,Matrix.conjTranspose_mul,Matrix.mul_assoc,center_scale]
  rw [show (1/sourceUnit center)*c=c/sourceUnit center by ring]

/-- Every coefficient at or below the rational threshold has a negative complete-source direction. -/
theorem loaded_negative {c : ℝ} (hc : c/sourceUnit center ≤ -100) :
    ∃ v : Fin 5 → ℝ, v ⬝ᵥ (normalizedGram center (loadedSource c) *ᵥ v) < 0 := by
  obtain ⟨v,hv⟩ := QuarticSixUpper.model_negative
  have hs := (abs_le.mp (source_error v)).2
  have hV := (loadGram_posSemidef 6).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hV
  have hcoef := mul_le_mul_of_nonneg_right hc hV
  rw [polyModel_eq (by norm_num : (6 : ℝ) ≠ 0)] at hv
  refine ⟨v,?_⟩
  rw [normalized_loaded]
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul,smul_eq_mul] at hv ⊢
  have he : v ⬝ᵥ v=∑ i, v i^2 := by simp only [dotProduct,pow_two]
  rw [he] at hv
  dsimp only [weight] at hs
  linarith only [hv,hs,hcoef]

/-- Gaussian negativity excludes nonnegativity in the original coordinates. -/
theorem loaded_not_posSemidef {c : ℝ} (hc : c/sourceUnit center ≤ -100) :
    ¬ (loadedSource c).PosSemidef := by
  intro h
  obtain ⟨v,hv⟩ := loaded_negative hc
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hp : (normalizedGram center (loadedSource c)).PosSemidef := by
    rw [normalizedGram_eq_congruence,center_scale]
    exact (h.conjTranspose_mul_mul_same (nativeBasis 6)).smul (by positivity)
  have hn := hp.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hn
  exact (not_lt_of_ge hn) hv

/-- The quartic repaired source fails already at theta scale six. -/
theorem repair_not_posSemidef : ¬ (FifthPolynomialCross.repair center).PosSemidef := by
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hc : FifthPolynomialCross.compensation center/sourceUnit center ≤ -100 := by
    apply (div_le_iff₀ hK).mpr
    have h := FifthPolynomialCross.compensation_six_upper center_scale
    nlinarith only [h,hK.le]
  exact loaded_not_posSemidef hc

/-- The literal truncated quartic source fails at every critical aperture. -/
theorem truncated_weightedRepair_not_posSemidef {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ¬ (FifthTruncatedCross.weightedRepair a (2*center)).PosSemidef := by
  have hcut1 : 1 ≤ FifthTruncatedCross.cutoff := by
    by_contra h
    have hs := mul_self_le_mul_self FifthTruncatedCross.cutoff_nonneg (not_le.mp h).le
    nlinarith only [hs,FifthTruncatedCross.cutoff_sq]
  have hcut : 2*center ≤ FifthTruncatedCross.cutoff :=
    (show 2*center ≤ 1 by linarith only [center_le_third]).trans hcut1
  rw [FifthTruncatedCross.weightedRepair_eq_inner a hcut]
  let w := 2*center*Real.sinh (a*(2*center))
  have hw : 0 < w := mul_pos (mul_pos (by norm_num) center_pos)
    (Real.sinh_pos_iff.mpr (mul_pos ha0 (mul_pos (by norm_num) center_pos)))
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hc : (deriv (FifthPolynomialCross.flux a) (2*center)/w)/sourceUnit center ≤ -100 := by
    apply (div_le_iff₀ hK).mpr
    apply (div_le_iff₀ hw).mpr
    have h := weighted_derivative_upper ha0.le ha
    change _ ≤ w*(-120*sourceUnit center) at h
    nlinarith only [h,mul_nonneg hw.le hK.le]
  intro h
  have he : (1/w) • FifthPolynomialCross.weightedRepair a (2*center)=
      loadedSource (deriv (FifthPolynomialCross.flux a) (2*center)/w) := by
    ext i j
    simp only [FifthPolynomialCross.weightedRepair,loadedSource,Matrix.add_apply,
      Matrix.smul_apply,smul_eq_mul,show 2*center/2=center by ring]
    change 1/w*(w*nativeShiftedMatrix 5 0 center i j+
      deriv (FifthPolynomialCross.flux a) (2*center)*
        EvenFiveEndpoint.crossLoad EvenFiveEndpoint.paidSevenSchur i j) = _
    field_simp [hw.ne']
  have hp := h.smul (show 0 ≤ 1/w by positivity)
  rw [he] at hp
  exact loaded_not_posSemidef hc hp

/-- Exact scalar brackets for the normalized complete quartic compensation. -/
theorem normalized_compensation_bounds :
    -(126 : ℝ) ≤ FifthPolynomialCross.compensation center/sourceUnit center ∧
      FifthPolynomialCross.compensation center/sourceUnit center ≤ -(1251/10) := by
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  constructor
  · apply (le_div_iff₀ hK).mpr
    exact FifthPolynomialCross.compensation_six_lower center_scale
  · apply (div_le_iff₀ hK).mpr
    exact FifthPolynomialCross.compensation_six_upper center_scale

/-- The complete source with a scalar multiple of the fixed two-coordinate load. -/
def scaledSource (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeShiftedMatrix 5 0 center+(t*FifthPolynomialCross.compensation center) •
    EvenFiveEndpoint.crossLoad EvenFiveEndpoint.paidSevenSchur

/-- The same complete loaded source in normalized Gaussian coordinates. -/
def scaledGram (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  normalizedGram center (scaledSource t)

theorem scaledGram_eq (t : ℝ) : scaledGram t = sourceGram center+
    (t*(FifthPolynomialCross.compensation center/sourceUnit center)) • loadGram 6 := by
  simp only [scaledGram,sourceGram,scaledSource,normalizedGram_eq_congruence,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,smul_add,smul_smul,
    loadGram,EvenFiveEndpoint.crossLoad,Matrix.conjTranspose_mul,Matrix.mul_assoc,center_scale]
  rw [show (1/sourceUnit center)*(t*FifthPolynomialCross.compensation center)=
    t*(FifthPolynomialCross.compensation center/sourceUnit center) by ring]

theorem scaledGram_hermitian (t : ℝ) : (scaledGram t).IsHermitian := by
  rw [scaledGram_eq]
  apply Matrix.IsHermitian.add
  · exact (sourceGram_posDef (x := center) (by rw [center_scale]; norm_num)).isHermitian
  · exact (loadGram_posSemidef 6).isHermitian.smul (by rfl)

theorem compensation_negative : FifthPolynomialCross.compensation center < 0 := by
  have hu := normalized_compensation_bounds.2
  have hn : -(1251/10 : ℝ) < 0 := by norm_num
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have h := (div_lt_iff₀ hK).mp (hu.trans_lt hn)
  simpa only [zero_mul] using h

/-- The full quartic load is beyond the complete-source positivity interval. -/
theorem full_load_negative : ∃ v : Fin 5 → ℝ, v ⬝ᵥ (scaledGram 1 *ᵥ v) < 0 := by
  have hc : FifthPolynomialCross.compensation center/sourceUnit center ≤ -100 :=
    normalized_compensation_bounds.2.trans (by norm_num)
  simpa only [scaledGram,scaledSource,loadedSource,one_mul] using loaded_negative hc

/-- The explicit coefficient cannot make the complete source nonnegative at every scale. -/
theorem full_load_not_posSemidef : ¬ (scaledGram 1).PosSemidef := by
  intro h
  obtain ⟨v,hv⟩ := full_load_negative
  have hn := h.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hn
  exact (not_lt_of_ge hn) hv

private theorem basis_inverse : nativeBasis 6*(nativeBasis 6)⁻¹=1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (nativeBasis_det_pos (by norm_num : (0 : ℝ)<6)).ne')

private theorem inverse_basis : (nativeBasis 6)⁻¹*nativeBasis 6=1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (nativeBasis_det_pos (by norm_num : (0 : ℝ)<6)).ne')

private theorem basis_injective : Function.Injective (nativeBasis 6).mulVec := by
  intro v w h
  have hh := congrArg (fun u => (nativeBasis 6)⁻¹ *ᵥ u) h
  simpa only [Matrix.mulVec_mulVec,inverse_basis,Matrix.one_mulVec] using hh

private theorem inverse_injective : Function.Injective ((nativeBasis 6)⁻¹).mulVec := by
  intro v w h
  have hh := congrArg (fun u => nativeBasis 6 *ᵥ u) h
  simpa only [Matrix.mulVec_mulVec,basis_inverse,Matrix.one_mulVec] using hh

private theorem recover_normalized (A : Matrix (Fin 5) (Fin 5) ℝ) :
    sourceUnit center • (((nativeBasis 6)⁻¹)ᴴ * normalizedGram center A * (nativeBasis 6)⁻¹)=A := by
  rw [normalizedGram_eq_congruence,center_scale]
  simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul]
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  rw [show sourceUnit center*(1/sourceUnit center)=1 by field_simp [hK.ne'],one_smul]
  calc
    _ = (nativeBasis 6*(nativeBasis 6)⁻¹)ᴴ*A*(nativeBasis 6*(nativeBasis 6)⁻¹) := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = A := by rw [basis_inverse]; simp

/-- Gaussian normalization preserves strict positivity of the complete loaded source. -/
theorem scaledGram_posDef_iff (t : ℝ) : (scaledGram t).PosDef ↔ (scaledSource t).PosDef := by
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  constructor
  · intro h
    have hp := (h.conjTranspose_mul_mul_same inverse_injective).smul hK
    change (sourceUnit center • (((nativeBasis 6)⁻¹)ᴴ * normalizedGram center (scaledSource t) * (nativeBasis 6)⁻¹)).PosDef at hp
    rw [recover_normalized] at hp
    exact hp
  · intro h
    rw [scaledGram,normalizedGram_eq_congruence,center_scale]
    exact (h.conjTranspose_mul_mul_same basis_injective).smul (by positivity)

/-- Gaussian normalization preserves nonnegativity of the complete loaded source. -/
theorem scaledGram_posSemidef_iff (t : ℝ) :
    (scaledGram t).PosSemidef ↔ (scaledSource t).PosSemidef := by
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  constructor
  · intro h
    have hp := (h.conjTranspose_mul_mul_same ((nativeBasis 6)⁻¹)).smul hK.le
    change (sourceUnit center • (((nativeBasis 6)⁻¹)ᴴ * normalizedGram center (scaledSource t) * (nativeBasis 6)⁻¹)).PosSemidef at hp
    rw [recover_normalized] at hp
    exact hp
  · intro h
    rw [scaledGram,normalizedGram_eq_congruence,center_scale]
    exact (h.conjTranspose_mul_mul_same (nativeBasis 6)).smul (by positivity)

end GaloisForLFunctions.ThetaCuspSections.SixSourceBounds
