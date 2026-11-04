import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightData
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCrossLoadPolynomialEnvelope

/-!
# Complete-source comparison at theta scale eight

The first three pure atoms, all retained unequal pairs, and the infinite tail
are compared with the exact rational matrices. Both sides of the normalized
compensation use the full source and its first derivative.
-/

noncomputable section
open Matrix RHTower
namespace GaloisForLFunctions.ThetaCuspSections.EightCrossSource
open FifthNativeRay FifthLeadingPair FifthRemainder EightCrossData FifthCrossEnvelope

/-- The center at which the first reflected atom has scale eight. -/
def center : ℝ := Real.log (8/Real.pi)/2

theorem center_scale : thetaCuspSingleAtomReflectionScale 1 center = 8 := by
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one,center]
  rw [show 2*(Real.log (8/Real.pi)/2)=Real.log (8/Real.pi) by ring,
    Real.exp_log (div_pos (by norm_num) Real.pi_pos)]
  field_simp [Real.pi_pos.ne']

theorem center_pos : 0 < center :=
  regimeOne_pos_of_six_le (by rw [center_scale]; norm_num)

theorem center_bounds : (14/15 : ℝ) ≤ 2*center ∧ 2*center ≤ 187/200 := by
  constructor
  · apply Real.exp_le_exp.mp
    apply (mul_le_mul_left Real.pi_pos).mp
    have hs : Real.pi*Real.exp (2*center)=8 := by
      simpa only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one] using center_scale
    rw [hs]
    exact center_lower_base
  · have h := center_tangent_eight center_pos.le
    have hs : Real.pi*Real.exp (2*center)=8 := by
      simpa only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one] using center_scale
    rw [hs] at h
    linarith only [h]

private theorem slope_at_center : firstSlope (thetaCuspSingleAtomReflectionScale 1 center)=287/26 := by
  rw [center_scale]
  norm_num [firstSlope]

private theorem derivative_upper :
    deriv thetaCuspFullSource center ≤ -(287/26-1/100000)*thetaCuspSourceTerm center 1 := by
  have hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 center := by rw [center_scale]; norm_num
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos center_pos (by norm_num : 0 < 1)
  have hε := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 1) (by norm_num) hq
  simp only [pow_one,center_scale] at hε
  have h := abs_thetaCuspFullSource_derivative_sub_first_le_effective 1 center_pos
    (by norm_num; rw [center_scale]; norm_num)
  simp only [iteratedDeriv_one,pow_one,first_derivative hq,slope_at_center,center_scale] at h
  have he : 36*8*regimeOneLikelihoodScale center ≤ (1/100000 : ℝ) := by
    linarith only [hε]
  have hm := mul_le_mul_of_nonneg_right he hf.le
  have hu := (abs_le.mp h).2
  nlinarith only [hu,hm]

/-- Two rational bounds on the complete normalized compensation. -/
theorem compensation_bounds :
    g 8 ≤ thetaCuspCenterCompensationSource center/sourceUnit center ∧
    thetaCuspCenterCompensationSource center/sourceUnit center ≤ upperCompensation := by
  let f := thetaCuspSourceTerm center 1
  let F := thetaCuspFullSource center
  have hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 center := by rw [center_scale]; norm_num
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos center_pos (by norm_num)
  have hF : 0 < F := thetaCuspFullSource_pos_all center
  have hb := mass_slope_bounds hq
  rw [slope_at_center] at hb
  change f ≤ F ∧ F ≤ (1000001/1000000)*f ∧
    -(287/26+1/100000)*f ≤ deriv thetaCuspFullSource center at hb
  have hsq : f^2=sourceUnit center*169 := by
    dsimp only [f]
    rw [first_mass_square,center_scale]
    norm_num
  have hFlo := mul_self_le_mul_self hf.le hb.1
  have hFhi := mul_self_le_mul_self hF.le hb.2.1
  have hFfLo := mul_le_mul_of_nonneg_right hb.1 hf.le
  have hFfHi := mul_le_mul_of_nonneg_right hb.2.1 hf.le
  have htl := mul_le_mul_of_nonneg_right center_bounds.1 (sq_nonneg f)
  have htu := mul_le_mul_of_nonneg_right center_bounds.2 (sq_nonneg f)
  constructor
  · apply (le_div_iff₀ hK).mpr
    have hd := mul_le_mul_of_nonneg_left hb.2.2
      (show 0 ≤ 2*center*F by positivity)
    have hfpay := mul_le_mul_of_nonneg_left hFfHi
      (show 0 ≤ 2*center*(287/26+1/100000) by positivity)
    have htpay := mul_le_mul_of_nonneg_left htu
      (by norm_num : (0 : ℝ) ≤ (1000001/1000000)*(287/26+1/100000))
    change g 8*sourceUnit center ≤ 3*F^2+2*center*F*deriv thetaCuspFullSource center
    norm_num [g]
    nlinarith only [hd,hFlo,hfpay,htpay,hsq]
  · apply (div_le_iff₀ hK).mpr
    have hd := mul_le_mul_of_nonneg_left derivative_upper
      (show 0 ≤ 2*center*F by positivity)
    have hfpay := mul_le_mul_of_nonneg_left hFfLo
      (show 0 ≤ 2*center*(287/26-1/100000) by positivity)
    have htpay := mul_le_mul_of_nonneg_left htl
      (by norm_num : (0 : ℝ) ≤ 287/26-1/100000)
    change 3*F^2+2*center*F*deriv thetaCuspFullSource center ≤ upperCompensation*sourceUnit center
    norm_num [upperCompensation]
    change _ ≤ _ at hd
    dsimp only [f,F] at hd ⊢
    dsimp only [f,F] at hFhi hfpay htpay hsq
    nlinarith only [hd,hFhi,hfpay,htpay,hsq]


private theorem pure_source_eq (n : ℕ) :
    FifthNativeRay.pureGram n center =
      ((n : ℝ)^4*Real.exp (-(2*(n : ℝ)^2-2)*8)) • EightCrossData.pureGram (8*(n : ℝ)^2) := by
  rw [FifthNativeRay.pureGram,normalizedGram,EightCrossData.pureGram,← gaussian_eq,← gaussianGram_smul]
  congr 1
  ext i j
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hj := _root_.RHTower.ThetaCuspOddFourThreeAtom.signed_pair_even n n (i.val+j.val) center
  rw [center_scale] at hj
  have hp :
      (thetaPairRadialEvenPolynomial ((n : ℝ)^2*(n : ℝ)^2*8^2) (i.val+j.val)).eval
        (((n : ℝ)^2+(n : ℝ)^2)*8) = rMoment (8*(n : ℝ)^2) (i.val+j.val) := by
    convert radial_eq (8*(n : ℝ)^2) (i.val+j.val) (by omega) using 1 <;> ring
  rw [hp] at hj
  have he : Real.exp (center-((n : ℝ)^2+(n : ℝ)^2)*8) =
      Real.exp (center-2*8)*Real.exp (-(2*(n : ℝ)^2-2)*8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hj
  simp only [FifthNativeRay.pureMatrix,center_scale,Matrix.smul_apply,smul_eq_mul]
  rw [hj]
  have hk : sourceUnit center=4*8^2*Real.exp (center-2*8) := by
    simp only [sourceUnit,center_scale]
  rw [hk]
  field_simp [Real.exp_ne_zero]
  ring

private theorem pure_two_small (i j : Fin 5) :
    |FifthNativeRay.pureGram 2 center i j| ≤ (1/1000 : ℝ) := by
  have he : Real.exp (-48 : ℝ)=Real.exp (-24 : ℝ)^2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [pure_source_eq]
  norm_num only [Nat.cast_ofNat,show (8 : ℝ)*2^2=32 by norm_num,
    show (2 : ℝ)^4=16 by norm_num,show -(2*(2 : ℝ)^2-2)*8=-48 by norm_num,
    Matrix.smul_apply,smul_eq_mul]
  rw [abs_mul,abs_of_pos (by positivity : (0 : ℝ)<16*Real.exp (-48))]
  have hz := pow_le_pow_left₀ (Real.exp_pos (-24)).le decay_bounds.2 2
  rw [← he] at hz
  calc
    _ ≤ (16*weight^2)*10000000000000000 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num)) (pure_two_bound i j)
        (abs_nonneg _) (by positivity)
    _ ≤ _ := by norm_num [weight]

private theorem pure_three_small (i j : Fin 5) :
    |FifthNativeRay.pureGram 3 center i j| ≤ (1/1000 : ℝ) := by
  have he : Real.exp (-72 : ℝ)=Real.exp (-24 : ℝ)^3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hz := pow_le_pow_left₀ (Real.exp_pos (-24)).le decay_bounds.2 3
  rw [← he] at hz
  have hz' : Real.exp (-128 : ℝ) ≤ weight^3 :=
    (Real.exp_le_exp.mpr (by norm_num : (-128 : ℝ) ≤ -72)).trans hz
  rw [pure_source_eq]
  norm_num only [Nat.cast_ofNat,show (8 : ℝ)*3^2=72 by norm_num,
    show (3 : ℝ)^4=81 by norm_num,show -(2*(3 : ℝ)^2-2)*8=-128 by norm_num,
    Matrix.smul_apply,smul_eq_mul]
  rw [abs_mul,abs_of_pos (by positivity : (0 : ℝ)<81*Real.exp (-128))]
  calc
    _ ≤ (81*weight^3)*1000000000000000000000000 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hz' (by norm_num)) (pure_three_bound i j)
        (abs_nonneg _) (by positivity)
    _ ≤ _ := by norm_num [weight]

private theorem weight_error : |Real.exp (-24 : ℝ)-weight| ≤ (1/1000000000000000000 : ℝ) := by
  rw [abs_of_nonpos (sub_nonpos.mpr decay_bounds.2)]
  have hl := decay_bounds.1
  norm_num [weight] at hl ⊢
  linarith only [hl]

private theorem leading_error (i j : Fin 5) :
    |(gaussianGram (leadingMatrix 8 (Real.exp (-24)))-
      gaussianGram (leadingMatrix 8 weight)) i j| ≤ (1/100 : ℝ) := by
  rw [leading_weight_difference]
  simp only [Matrix.smul_apply,smul_eq_mul,abs_mul]
  have h := mul_le_mul weight_error (mixed_bound i j) (abs_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1/1000000000000000000)
  norm_num at h
  exact h

private theorem source_error_entry (i j : Fin 5) :
    |(sourceGram center-gaussianGram (leadingMatrix 8 weight)) i j| ≤ (1/50 : ℝ) := by
  have hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 center := by rw [center_scale]; norm_num
  have hd := sourceGram_decomposition hq
  rw [center_scale] at hd
  norm_num only [show (-3 : ℝ)*8=-24 by norm_num] at hd
  have hr := remainderGram_bound hq i j
  have hp2 := pure_two_small i j
  have hp3 := pure_three_small i j
  have he := leading_error i j
  have hid : (sourceGram center-gaussianGram (leadingMatrix 8 weight)) i j =
      ((gaussianGram (leadingMatrix 8 (Real.exp (-24)))-gaussianGram (leadingMatrix 8 weight)) i j+
        remainderGram center i j)+FifthNativeRay.pureGram 2 center i j+FifthNativeRay.pureGram 3 center i j := by
    rw [hd]
    simp only [Matrix.add_apply,Matrix.sub_apply]
    ring
  rw [hid]
  exact (abs_add _ _).trans ((add_le_add_right ((abs_add _ _).trans
    (add_le_add_right ((abs_add _ _).trans (add_le_add he hr)) _)) _).trans
      (by linarith only [hp2,hp3]))

/-- The complete native source lies within one tenth of the retained Gaussian form. -/
theorem source_error (v : Fin 5 → ℝ) :
    |v ⬝ᵥ (sourceGram center *ᵥ v)-v ⬝ᵥ (gaussianGram (leadingMatrix 8 weight) *ᵥ v)| ≤
      (1/10 : ℝ)*(∑ i, v i^2) := by
  have h := _root_.RHTower.abs_dotProduct_mulVec_le
    (sourceGram center-gaussianGram (leadingMatrix 8 weight)) (by norm_num : (0 : ℝ) ≤ 1/50)
    source_error_entry v
  norm_num only [Matrix.sub_mulVec,dotProduct_sub,Fintype.card_fin,Nat.cast_ofNat] at h
  simpa only [show (5 : ℝ)*(1/50)=1/10 by norm_num] using h


/-- The complete source with a scalar multiple of the fixed two-coordinate load. -/
def scaledSource (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeShiftedMatrix 5 0 center+(t*thetaCuspCenterCompensationSource center) •
    EvenFiveEndpoint.crossLoad EvenFiveEndpoint.paidSevenSchur

/-- The same complete loaded source in normalized Gaussian coordinates. -/
def scaledGram (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  normalizedGram center (scaledSource t)

theorem scaledGram_eq (t : ℝ) : scaledGram t = sourceGram center+
    (t*(thetaCuspCenterCompensationSource center/sourceUnit center)) • loadGram 8 := by
  simp only [scaledGram,sourceGram,scaledSource,normalizedGram_eq_congruence,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,smul_add,smul_smul,
    loadGram,EvenFiveEndpoint.crossLoad,Matrix.conjTranspose_mul,Matrix.mul_assoc,center_scale]
  rw [show (1/sourceUnit center)*(t*thetaCuspCenterCompensationSource center)=
    t*(thetaCuspCenterCompensationSource center/sourceUnit center) by ring]

theorem scaledGram_hermitian (t : ℝ) : (scaledGram t).IsHermitian := by
  rw [scaledGram_eq]
  apply Matrix.IsHermitian.add
  · exact (sourceGram_posDef (x := center) (by rw [center_scale]; norm_num)).isHermitian
  · exact (loadGram_posSemidef 8).isHermitian.smul (by rfl)

theorem compensation_negative : thetaCuspCenterCompensationSource center < 0 := by
  have hu := compensation_bounds.2
  have hn : upperCompensation < 0 := by norm_num [upperCompensation]
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have h := (div_lt_iff₀ hK).mp (hu.trans_lt hn)
  simpa only [zero_mul] using h

/-- Half the fixed load remains strictly positive for the complete source. -/
theorem half_load_posDef : (scaledGram (1/2)).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨scaledGram_hermitian _,?_⟩
  intro v hv
  have hl := lowerEight_posDef.dotProduct_mulVec_pos hv
  have hs := (abs_le.mp (source_error v)).1
  have hV := (loadGram_posSemidef 8).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hl hV ⊢
  have hc := mul_le_mul_of_nonneg_right compensation_bounds.1 hV
  rw [lowerEight,polyModel_eq (by norm_num)] at hl
  rw [scaledGram_eq]
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul,smul_eq_mul] at hl ⊢
  have he : v ⬝ᵥ v=∑ i, v i^2 := by simp only [dotProduct,pow_two]
  rw [he] at hl
  nlinarith only [hl,hs,hc]

/-- The full fixed load has a negative direction in the complete source. -/
theorem full_load_negative : ∃ v : Fin 5 → ℝ, v ⬝ᵥ (scaledGram 1 *ᵥ v) < 0 := by
  obtain ⟨v,hv⟩ := upperEight_negative
  have hs := (abs_le.mp (source_error v)).2
  have hV := (loadGram_posSemidef 8).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hV
  have hc := mul_le_mul_of_nonneg_right compensation_bounds.2 hV
  rw [upperEight,polyModel_eq (by norm_num)] at hv
  refine ⟨v,?_⟩
  rw [scaledGram_eq]
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul,smul_eq_mul,one_mul] at hv ⊢
  have he : v ⬝ᵥ v=∑ i, v i^2 := by simp only [dotProduct,pow_two]
  rw [he] at hv
  linarith only [hv,hs,hc]

/-- The explicit coefficient cannot make the complete source nonnegative at every scale. -/
theorem full_load_not_posSemidef : ¬ (scaledGram 1).PosSemidef := by
  intro h
  obtain ⟨v,hv⟩ := full_load_negative
  have hn := h.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hn
  exact (not_lt_of_ge hn) hv


private theorem basis_inverse : nativeBasis 8*(nativeBasis 8)⁻¹=1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (nativeBasis_det_pos (by norm_num : (0 : ℝ)<8)).ne')

private theorem inverse_basis : (nativeBasis 8)⁻¹*nativeBasis 8=1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (nativeBasis_det_pos (by norm_num : (0 : ℝ)<8)).ne')

private theorem basis_injective : Function.Injective (nativeBasis 8).mulVec := by
  intro v w h
  have hh := congrArg (fun u => (nativeBasis 8)⁻¹ *ᵥ u) h
  simpa only [Matrix.mulVec_mulVec,inverse_basis,Matrix.one_mulVec] using hh

private theorem inverse_injective : Function.Injective ((nativeBasis 8)⁻¹).mulVec := by
  intro v w h
  have hh := congrArg (fun u => nativeBasis 8 *ᵥ u) h
  simpa only [Matrix.mulVec_mulVec,basis_inverse,Matrix.one_mulVec] using hh

private theorem recover_normalized (A : Matrix (Fin 5) (Fin 5) ℝ) :
    sourceUnit center • (((nativeBasis 8)⁻¹)ᴴ * normalizedGram center A * (nativeBasis 8)⁻¹)=A := by
  rw [normalizedGram_eq_congruence,center_scale]
  simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul]
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  rw [show sourceUnit center*(1/sourceUnit center)=1 by field_simp [hK.ne'],one_smul]
  calc
    _ = (nativeBasis 8*(nativeBasis 8)⁻¹)ᴴ*A*(nativeBasis 8*(nativeBasis 8)⁻¹) := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = A := by rw [basis_inverse]; simp

/-- Gaussian normalization preserves strict positivity of the complete loaded source. -/
theorem scaledGram_posDef_iff (t : ℝ) : (scaledGram t).PosDef ↔ (scaledSource t).PosDef := by
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  constructor
  · intro h
    have hp := (h.conjTranspose_mul_mul_same inverse_injective).smul hK
    change (sourceUnit center • (((nativeBasis 8)⁻¹)ᴴ * normalizedGram center (scaledSource t) * (nativeBasis 8)⁻¹)).PosDef at hp
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
    have hp := (h.conjTranspose_mul_mul_same ((nativeBasis 8)⁻¹)).smul hK.le
    change (sourceUnit center • (((nativeBasis 8)⁻¹)ᴴ * normalizedGram center (scaledSource t) * (nativeBasis 8)⁻¹)).PosSemidef at hp
    rw [recover_normalized] at hp
    exact hp
  · intro h
    rw [scaledGram,normalizedGram_eq_congruence,center_scale]
    exact (h.conjTranspose_mul_mul_same (nativeBasis 8)).smul (by positivity)

/-- Half the explicit fixed coefficient is admissible at scale eight. -/
theorem source_half_load_posDef : (scaledSource (1/2)).PosDef :=
  (scaledGram_posDef_iff _).mp half_load_posDef

/-- The complete fixed endpoint-compatible cross-load fails at scale eight. -/
theorem crossRepair_not_posSemidef : ¬ (EvenFiveEndpoint.crossRepair center).PosSemidef := by
  have he : EvenFiveEndpoint.crossRepair center=scaledSource 1 := by
    simp only [EvenFiveEndpoint.crossRepair,scaledSource,one_mul]
  rw [he,← scaledGram_posSemidef_iff]
  exact full_load_not_posSemidef

end GaloisForLFunctions.ThetaCuspSections.EightCrossSource
