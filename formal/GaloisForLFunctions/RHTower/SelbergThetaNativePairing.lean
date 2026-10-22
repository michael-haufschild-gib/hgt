import GaloisForLFunctions.RHTower.SelbergThetaNativeMoments
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMStripMeanAdmission

/-!
# Nonzero native theta source from its complete Eisenstein pairing

Absolute primitive-row unfolding and all-real Mellin moments evaluate both
Weyl terms of the actual centered source. Their algebra proves native
nonvanishing, strict positive weighted energy and actual unit normalization.
No operator equation or spectral occurrence is assumed.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.SelbergThetaNativePairing
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse
open SelbergThetaNativeSource SelbergThetaNativeEnergy SelbergThetaNativeMoments
noncomputable section

private def k : ℝ := cuspReflectionNorm 2

private theorem k_pos : 0 < k := by
  unfold k cuspReflectionNorm
  apply div_pos <;> apply norm_pos_iff.mpr <;>
    apply cuspCompletedLambda_ne_zero <;> norm_num

private theorem completion_ratio : reflectedCompletedLambda 3 = reflectedCompletedLambda 4*(k:ℂ) := by
  have he := lowCuspPower_completed_mean ⟨(2:ℂ),by norm_num⟩ 2 (by norm_num)
  have hc (z : UpperHalfPlane) : (positiveLowCuspRows 2 z:ℂ) =
      periodize (cuspHeightSeed (lowCuspPower (2:ℂ))) z := by
    simpa using positiveLowCuspRows_coe 2 (by norm_num) z
  simp_rw [← hc] at he
  rw [integral_const_mul,integral_complex_ofReal,positiveLowCuspRows_mean 2 (by norm_num) (by norm_num)] at he
  norm_num [k,Complex.cpow_neg_one] at he ⊢
  linear_combination -2*he

private theorem principal_two (y : ℝ) :
    principal (3/2:ℂ) ![0,y] =
      reflectedCompletedLambda 3*(y:ℂ)^(-1:ℂ)+reflectedCompletedLambda 4*(y:ℂ)^2 := by
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCompletedEisensteinCuspConstantMaassFactor,d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign,Bool.false_eq_true,if_false,if_true,mul_one]
  norm_num only
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  norm_num

private theorem positive_mean {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0:ℝ) 1, positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ))) = y^2+k*y^(-1:ℝ) := by
  apply Complex.ofReal_injective
  apply mul_left_cancel₀ (cuspCompletedLambda_ne_zero (by norm_num : 1 < (4:ℂ).re))
  have he := positiveCuspRows_completed_mean 2 (by norm_num) hy
  norm_num only [Complex.ofReal_ofNat] at he
  rw [he,principal_two,completion_ratio]
  simp only [Complex.cpow_neg_one,Real.rpow_neg_one]
  push_cast
  ring

private theorem positive_invariant (g : PSL2Z) (z : UpperHalfPlane) :
    positiveCuspRows 2 (g • z) = positiveCuspRows 2 z := by
  apply Complex.ofReal_injective
  rw [positiveCuspRows_coe 2 (by norm_num),positiveCuspRows_coe 2 (by norm_num)]
  exact periodize_invariant _ g z

private theorem profile_power_integrable (h : ℝ → ℂ) (hm : Measurable h)
    (hb : ∀ r : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^r) (r : ℝ) :
    IntegrableOn (fun y : ℝ => ‖h y‖*y^r) (Ioi (0:ℝ)) := by
  have hmeas : Measurable (fun y : ℝ => ‖h y‖*y^r) := by fun_prop
  obtain ⟨C,_,hC⟩ := hb (-r)
  obtain ⟨D,_,hD⟩ := hb (-2-r)
  have hsmall : IntegrableOn (fun y : ℝ => ‖h y‖*y^r) (Ioc (0:ℝ) 1) := by
    apply (integrable_const C).mono' hmeas.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hy.1.le _))]
    calc
      _ ≤ (C*y^(-r))*y^r := mul_le_mul_of_nonneg_right (hC y hy.1) (Real.rpow_nonneg hy.1.le _)
      _ = C := by rw [mul_assoc,← Real.rpow_add hy.1]; simp
  have hlarge : IntegrableOn (fun y : ℝ => ‖h y‖*y^r) (Ioi (1:ℝ)) := by
    apply ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1)
      (by norm_num : (0:ℝ)<1)).const_mul D).mono' hmeas.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := lt_trans zero_lt_one hy
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hy0.le _))]
    calc
      _ ≤ (D*y^(-2-r))*y^r := mul_le_mul_of_nonneg_right (hD y hy0) (Real.rpow_nonneg hy0.le _)
      _ = D*y^(-2:ℝ) := by rw [mul_assoc,← Real.rpow_add hy0]; congr 2; ring
  apply (hsmall.union hlarge).mono_set
  intro y hy
  rcases le_or_gt y 1 with h | h
  · exact Or.inl ⟨hy,h⟩
  · exact Or.inr h

private theorem point_im (x y : ℝ) (hy : 0 < y) :
    (ofComplex (⟨x,y⟩:ℂ)).im=y := by
  rw [ofComplex_apply_of_im_pos hy]
  rfl

private theorem product_strip_integrable (h : ℝ → ℂ) (hm : Measurable h)
    (hb : ∀ r : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^r) :
    IntegrableOn (fun z : UpperHalfPlane => h z.im*(positiveCuspRows 2 z:ℂ)) modularStrip volume := by
  have hmeas : Measurable (fun z : UpperHalfPlane => h z.im*(positiveCuspRows 2 z:ℂ)) :=
    (hm.comp UpperHalfPlane.continuous_im.measurable).mul
      (Complex.continuous_ofReal.measurable.comp (positiveCuspRows_measurable 2))
  apply modularStrip_integrable_of_norm_mean _ hmeas
  · intro y hy
    have hi := (positiveCuspRows_horizontal_integrable 2 (by norm_num) hy).ofReal.const_mul (h y)
    simpa only [point_im _ _ hy] using! hi
  · have hi := (profile_power_integrable h hm hb 0).add
      ((profile_power_integrable h hm hb (-3)).const_mul k)
    apply hi.congr_fun _ measurableSet_Ioi
    intro y hy
    have he : (∫ x in Ico (0:ℝ) 1,
        ‖h (ofComplex (⟨x,y⟩:ℂ)).im*(positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ)):ℂ)‖) =
        ‖h y‖*(y^2+k*y^(-1:ℝ)) := by
      simp only [point_im _ _ hy,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (positiveCuspRows_nonneg 2 _)]
      rw [integral_const_mul,positive_mean hy]
    simp only [Pi.add_apply]
    rw [he]
    simp only [Real.rpow_zero,mul_one,Real.rpow_neg_one]
    rw [show y^(-3:ℝ)=(y^3)⁻¹ by rw [Real.rpow_neg hy.le]; norm_num]
    have hy0 : 0 < y := hy
    field_simp [hy0.ne']

private theorem profile_rows_summable (h : ℝ → ℂ)
    (hb : ∀ r : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^r)
    (z : UpperHalfPlane) : Summable (fun v : gammaSetHalf => h (gammaSetMatrix v.1 • z).im) := by
  obtain ⟨C,_,hC⟩ := hb 2
  apply Summable.of_norm_bounded ((positiveCuspRows_summable 2 (by norm_num) z).mul_left C)
  intro v
  exact hC _ (gammaSetMatrix v.1 • z).im_pos

private theorem product_unfold (h : ℝ → ℂ) (hm : Measurable h)
    (hb : ∀ r : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^r) :
    (∫ z, periodize (cuspHeightSeed h) z*(positiveCuspRows 2 z:ℂ) ∂angularMeasure) =
      ∫ z in modularStrip, h z.im*(positiveCuspRows 2 z:ℂ) := by
  let φ : UpperHalfPlane → ℂ := fun z => h z.im*(positiveCuspRows 2 z:ℂ)
  have hφ : IntegrableOn φ modularStrip volume := product_strip_integrable h hm hb
  have hp (n : ℤ) (z : UpperHalfPlane) : φ (ModularGroup.T^n • z)=φ z := by
    change h (ModularGroup.T^n • z).im*(positiveCuspRows 2 (ModularGroup.T^n • z):ℂ) =
      h z.im*(positiveCuspRows 2 z:ℂ)
    rw [im_T_zpow_smul]
    have he := positive_invariant (QuotientGroup.mk (ModularGroup.T^n):PSL2Z) z
    simpa only [PSL2Z_mk_smul] using congrArg (fun t : ℝ => h z.im*(t:ℂ)) he
  have hr (v : gammaSetHalf) (z : UpperHalfPlane) :
      φ (gammaSetMatrix v.1 • z)=h (gammaSetMatrix v.1 • z).im*(positiveCuspRows 2 z:ℂ) := by
    change h (gammaSetMatrix v.1 • z).im*(positiveCuspRows 2 (gammaSetMatrix v.1 • z):ℂ) =
      h (gammaSetMatrix v.1 • z).im*(positiveCuspRows 2 z:ℂ)
    have he := positive_invariant (QuotientGroup.mk (gammaSetMatrix v.1):PSL2Z) z
    rw [PSL2Z_mk_smul] at he
    rw [he]
  have hrow (v : gammaSetHalf) :
      Integrable (fun z : UpperHalfPlane => φ (gammaSetMatrix v.1 • z)) angularMeasure :=
    (integrableOn_smul_set_iff _ _ _).mp (integrableOn_smul_fd_of_periodic hp hφ _)
  have hnorm_periodic (n : ℤ) (z : UpperHalfPlane) :
      (‖φ (ModularGroup.T^n • z)‖:ℂ)=(‖φ z‖:ℂ) := by rw [hp]
  have hsum : Summable (fun v : gammaSetHalf =>
      ∫ z, ‖φ (gammaSetMatrix v.1 • z)‖ ∂angularMeasure) := by
    have hh := (Complex.reCLM.hasSum (hasSum_fdUnfoldTerm_half hnorm_periodic hφ.norm.ofReal)).summable
    convert hh using 1
    funext v
    change (∫ z, ‖φ (gammaSetMatrix v.1 • z)‖ ∂angularMeasure) =
      (∫ z, (‖φ (gammaSetMatrix v.1 • z)‖:ℂ) ∂angularMeasure).re
    have he : (∫ z, (‖φ (gammaSetMatrix v.1 • z)‖:ℂ) ∂angularMeasure) =
        ((∫ z, ‖φ (gammaSetMatrix v.1 • z)‖ ∂angularMeasure:ℝ):ℂ) := integral_ofReal
    rw [he,Complex.ofReal_re]
  have ht := (hasSum_integral_of_summable_integral_norm hrow hsum).tsum_eq
  have hu := (hasSum_fdUnfoldTerm_half hp hφ).tsum_eq
  rw [← isFundamentalDomain_modularStrip.setIntegral_eq isFundamentalDomain_iUnion_halfRep_smul_fd
    (translationSubgroup_invariant_of_periodic hp)] at hu
  calc
    _ = ∫ z, ∑' v : gammaSetHalf, φ (gammaSetMatrix v.1 • z) ∂angularMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      simp_rw [hr]
      rw [tsum_mul_right,periodize_cuspHeightSeed_eq_rows_of_rows_summable h z
        (profile_rows_summable h hb z)]
    _ = _ := ht.symm.trans hu

private theorem profile_mellin_integrable (h : ℝ → ℂ) (hm : Measurable h)
    (hb : ∀ r : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^r) (r : ℝ) :
    IntegrableOn (fun y : ℝ => (y^2)⁻¹ • (h y*(y^r:ℝ))) (Ioi (0:ℝ)) := by
  have hmeas : Measurable (fun y : ℝ => (y^2)⁻¹ • (h y*(y^r:ℝ))) := by fun_prop
  apply (profile_power_integrable h hm hb (r-2)).mono' hmeas.aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro y hy
  rw [norm_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg y)),abs_of_nonneg (Real.rpow_nonneg hy.le _)]
  rw [Real.rpow_sub hy,Real.rpow_two]
  exact le_of_eq (by ring)

private theorem product_mellin (h : ℝ → ℂ) (hm : Measurable h)
    (hb : ∀ r : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^r) :
    (∫ z, periodize (cuspHeightSeed h) z*(positiveCuspRows 2 z:ℂ) ∂angularMeasure) =
      (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^(2:ℝ):ℝ)))+
        (k:ℂ)*(∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^(-1:ℝ):ℝ))) := by
  rw [product_unfold h hm hb,
    setIntegral_modularStrip_eq_iterated _ (product_strip_integrable h hm hb)]
  have he : (∫ y in Ioi (0:ℝ), (y^2)⁻¹ •
      ∫ x in Ico (0:ℝ) 1,
        h (ofComplex (⟨x,y⟩:ℂ)).im*(positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ)):ℂ)) =
      ∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^(2:ℝ):ℝ))+
        (k:ℂ)*((y^2)⁻¹ • (h y*(y^(-1:ℝ):ℝ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [point_im _ _ hy]
    rw [integral_const_mul,integral_complex_ofReal,positive_mean hy]
    simp only [Real.rpow_two,Complex.real_smul,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  rw [he]
  have hs : (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^(2:ℝ):ℝ))+
      (k:ℂ)*((y^2)⁻¹ • (h y*(y^(-1:ℝ):ℝ)))) =
      (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^(2:ℝ):ℝ)))+
        (∫ y in Ioi (0:ℝ), (k:ℂ)*((y^2)⁻¹ • (h y*(y^(-1:ℝ):ℝ)))) := by
    simpa using! integral_add (profile_mellin_integrable h hm hb 2)
      ((profile_mellin_integrable h hm hb (-1)).const_mul (k:ℂ))
  rw [hs,integral_const_mul]

private theorem positiveProfile_measurable : Measurable positiveProfile := by
  unfold positiveProfile
  exact ((Real.measurable_log.div_const 2).exp).mul
    (contDiff_thetaCuspFullSource.continuous.measurable.comp (Real.measurable_log.div_const 2))

private theorem modeProfile_measurable (q : XiZeroCopy) : Measurable (modeProfile q) := by
  unfold modeProfile
  exact (Complex.continuous_ofReal.measurable.comp positiveProfile_measurable).mul
    ((SelbergThetaSourceVariance.continuous_sourceRatio q).measurable.comp (Real.measurable_log.div_const 2))

private theorem positiveProfile_norm_bounds (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖(positiveProfile y:ℂ)‖ ≤ C*y^r := by
  obtain ⟨C,hC0,hC⟩ := positiveProfile_power_bound r
  refine ⟨C,hC0,?_⟩
  intro y hy
  have hp : 0 < positiveProfile y := mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  exact hC y hy

private def centeredProfile (q : XiZeroCopy) (y : ℝ) : ℂ :=
  modeProfile q y+(positiveProfile y:ℂ)/(xiSpectralPoint q-Complex.I)

private theorem centeredProfile_measurable (q : XiZeroCopy) : Measurable (centeredProfile q) :=
  (modeProfile_measurable q).add
    ((Complex.continuous_ofReal.measurable.comp positiveProfile_measurable).div_const _)

private theorem centeredProfile_bounds (q : XiZeroCopy) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖centeredProfile q y‖ ≤ C*y^r := by
  obtain ⟨C,hC0,hC⟩ := modeProfile_power_bound q r
  obtain ⟨D,hD0,hD⟩ := positiveProfile_norm_bounds r
  refine ⟨C+D*‖(xiSpectralPoint q-Complex.I)⁻¹‖,
    add_pos_of_pos_of_nonneg hC0 (mul_nonneg hD0.le (norm_nonneg _)),?_⟩
  intro y hy
  calc
    _ ≤ ‖modeProfile q y‖+‖(positiveProfile y:ℂ)/(xiSpectralPoint q-Complex.I)‖ := norm_add_le _ _
    _ = ‖modeProfile q y‖+‖(positiveProfile y:ℂ)‖*‖(xiSpectralPoint q-Complex.I)⁻¹‖ := by
      rw [div_eq_mul_inv,norm_mul]
    _ ≤ C*y^r+(D*y^r)*‖(xiSpectralPoint q-Complex.I)⁻¹‖ :=
      add_le_add (hC y hy) (mul_le_mul_of_nonneg_right (hD y hy) (norm_nonneg _))
    _ = _ := by ring

private theorem centered_periodize (q : XiZeroCopy) (z : UpperHalfPlane) :
    periodize (cuspHeightSeed (centeredProfile q)) z=centeredSource q z := by
  have hsW := profile_rows_summable (modeProfile q) (modeProfile_power_bound q) z
  have hsP := profile_rows_summable (fun y => (positiveProfile y:ℂ)) positiveProfile_norm_bounds z
  rw [periodize_cuspHeightSeed_eq_rows_of_rows_summable _ z
    (profile_rows_summable _ (centeredProfile_bounds q) z)]
  simp only [centeredProfile,div_eq_mul_inv]
  rw [hsW.tsum_add (hsP.mul_right _),tsum_mul_right,← Complex.ofReal_tsum]
  have hw := periodize_cuspHeightSeed_eq_rows_of_rows_summable (modeProfile q) z hsW
  change _ = modeSource q z+(positiveSource z:ℂ)*(xiSpectralPoint q-Complex.I)⁻¹
  rw [← hw]
  rfl

private theorem centered_mellin (q : XiZeroCopy) (r : ℝ) :
    (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (centeredProfile q y*(y^r:ℝ))) =
      -(tiltedMass (2*r-1):ℂ)/(xiSpectralPoint q+Complex.I*((2*r-1:ℝ):ℂ))+
        (tiltedMass (2*r-1):ℂ)/(xiSpectralPoint q-Complex.I) := by
  have he (y : ℝ) : (y^2)⁻¹ • (centeredProfile q y*(y^r:ℝ)) =
      (y^2)⁻¹ • (modeProfile q y*(y^r:ℝ))+
        ((y^2)⁻¹ • ((positiveProfile y:ℂ)*(y^r:ℝ)))/(xiSpectralPoint q-Complex.I) := by
    simp only [centeredProfile,Complex.real_smul,div_eq_mul_inv]
    ring
  simp_rw [he]
  have hp := profile_mellin_integrable (fun y => (positiveProfile y:ℂ))
    (Complex.continuous_ofReal.measurable.comp positiveProfile_measurable) positiveProfile_norm_bounds r
  have hs : (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (modeProfile q y*(y^r:ℝ))+
      ((y^2)⁻¹ • ((positiveProfile y:ℂ)*(y^r:ℝ)))/(xiSpectralPoint q-Complex.I)) =
      (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (modeProfile q y*(y^r:ℝ)))+
        (∫ y in Ioi (0:ℝ), ((y^2)⁻¹ • ((positiveProfile y:ℂ)*(y^r:ℝ)))/(xiSpectralPoint q-Complex.I)) := by
    simpa using! integral_add
      (profile_mellin_integrable (modeProfile q) (modeProfile_measurable q) (modeProfile_power_bound q) r)
      (hp.div_const _)
  rw [hs,integral_div,modeProfile_mellin,positiveProfile_mellin]

private theorem spectral_re_ne_zero (q : XiZeroCopy) : (xiSpectralPoint q).re ≠ 0 := by
  simpa [xiSpectralPoint,Complex.mul_re,Complex.mul_im] using xi_divisor_support_im_ne_zero q.1

private theorem shift_ne_zero (q : XiZeroCopy) (a : ℝ) :
    xiSpectralPoint q+Complex.I*(a:ℂ) ≠ 0 := by
  intro he
  apply spectral_re_ne_zero q
  have hr := congrArg Complex.re he
  simpa using hr

/-- The complete centered source has an exact two-Weyl pairing with the original positive Eisenstein field. -/
theorem centeredSource_pairing (q : XiZeroCopy) :
    (∫ z, centeredSource q z*(positiveCuspRows 2 z:ℂ) ∂angularMeasure) =
      (2*Complex.I*(tiltedMass 3:ℂ)/(xiSpectralPoint q-Complex.I))*
        (2/(xiSpectralPoint q+3*Complex.I)-
          (cuspReflectionNorm 2:ℂ)/(xiSpectralPoint q-3*Complex.I)) := by
  have he := product_mellin (centeredProfile q) (centeredProfile_measurable q) (centeredProfile_bounds q)
  simp_rw [centered_periodize] at he
  rw [centered_mellin,centered_mellin] at he
  norm_num only [Complex.ofReal_ofNat] at he
  rw [tiltedMass_neg] at he
  rw [he]
  have h0 : xiSpectralPoint q-Complex.I ≠ 0 := by
    simpa [sub_eq_add_neg] using shift_ne_zero q (-1)
  have h1 : xiSpectralPoint q+3*Complex.I ≠ 0 := by
    simpa [mul_comm] using shift_ne_zero q 3
  have h2 : xiSpectralPoint q-3*Complex.I ≠ 0 := by
    simpa [mul_comm,sub_eq_add_neg] using shift_ne_zero q (-3)
  dsimp [k]
  simp only [Complex.ofReal_neg,Complex.ofReal_ofNat,mul_neg,← sub_eq_add_neg,
    mul_comm Complex.I (3:ℂ)]
  field_simp [h0,h1,h2]
  ring

/-- The two Weyl terms cannot cancel at an actual Xi zero ordinate. -/
theorem centeredSource_pairing_ne_zero (q : XiZeroCopy) :
    (∫ z, centeredSource q z*(positiveCuspRows 2 z:ℂ) ∂angularMeasure) ≠ 0 := by
  rw [centeredSource_pairing]
  have h0 : xiSpectralPoint q-Complex.I ≠ 0 := by simpa [sub_eq_add_neg] using shift_ne_zero q (-1)
  have h1 : xiSpectralPoint q+3*Complex.I ≠ 0 := by simpa [mul_comm] using shift_ne_zero q 3
  have h2 : xiSpectralPoint q-3*Complex.I ≠ 0 := by simpa [mul_comm,sub_eq_add_neg] using shift_ne_zero q (-3)
  apply mul_ne_zero
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (tiltedMass_pos 3).ne')) h0
  · intro hz
    change 2/(xiSpectralPoint q+3*Complex.I)-(k:ℂ)/(xiSpectralPoint q-3*Complex.I)=0 at hz
    field_simp [h1,h2] at hz
    have hr := congrArg Complex.re hz
    have hi := congrArg Complex.im hz
    norm_num [Complex.mul_re,Complex.mul_im] at hr
    have hprod : (2-k)*(xiSpectralPoint q).re=0 := by nlinarith [hr]
    have hk : k=2 := by
      have hh := (mul_eq_zero.mp hprod).resolve_right (spectral_re_ne_zero q)
      linarith
    rw [hk] at hi
    norm_num [Complex.mul_im,Complex.mul_re] at hi
    linarith

/-- The actual centered source survives complete periodization in the native almost-everywhere sense. -/
theorem centeredSource_not_ae_zero (q : XiZeroCopy) :
    ¬ (centeredSource q =ᵐ[angularMeasure] fun _ => (0:ℂ)) := by
  intro hz
  apply centeredSource_pairing_ne_zero q
  have hp : (fun z => centeredSource q z*(positiveCuspRows 2 z:ℂ)) =ᵐ[angularMeasure] fun _ => (0:ℂ) := by
    filter_upwards [hz] with z hz
    rw [hz,zero_mul]
  rw [integral_congr_ae hp]
  simp

private theorem centered_density_integrable (q : XiZeroCopy) :
    Integrable (fun z => ‖centeredSource q z‖^2/positiveSource z) angularMeasure := by
  let K : ℝ := 2/|(xiSpectralPoint q).re|+‖(xiSpectralPoint q-Complex.I)⁻¹‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm : Measurable (centeredSource q) := (modeSource_measurable q).add
    ((Complex.continuous_ofReal.measurable.comp positiveSource_measurable).div_const _)
  have hP : Integrable positiveSource angularMeasure := MemLp.integrable (by norm_num) positiveSource_memLp
  apply (hP.const_mul (K^2)).mono' ((hm.norm.pow_const 2).div positiveSource_measurable).aestronglyMeasurable
  filter_upwards with z
  change ‖‖centeredSource q z‖^2/positiveSource z‖ ≤ K^2*positiveSource z
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (positiveSource_pos z).le)]
  have hb : ‖centeredSource q z‖ ≤ K*positiveSource z := by
    calc
      _ ≤ ‖modeSource q z‖+‖(positiveSource z:ℂ)/(xiSpectralPoint q-Complex.I)‖ := norm_add_le _ _
      _ = ‖modeSource q z‖+positiveSource z*‖(xiSpectralPoint q-Complex.I)⁻¹‖ := by
        rw [div_eq_mul_inv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positiveSource_pos z)]
      _ ≤ 2*positiveSource z/|(xiSpectralPoint q).re|+
          positiveSource z*‖(xiSpectralPoint q-Complex.I)⁻¹‖ :=
        add_le_add (modeSource_norm_lt q z).le le_rfl
      _ = _ := by dsimp [K]; ring
  apply (div_le_iff₀ (positiveSource_pos z)).2
  have hs : ‖centeredSource q z‖^2 ≤ (K*positiveSource z)^2 := by
    nlinarith [norm_nonneg (centeredSource q z),mul_nonneg hK (positiveSource_pos z).le]
  nlinarith [hs]

/-- The centered native theta source has strictly positive weighted energy. -/
theorem centeredEnergy_pos (q : XiZeroCopy) : 0 < centeredEnergy q := by
  by_contra hn
  have he : (∫ z, ‖centeredSource q z‖^2/positiveSource z ∂angularMeasure)=0 :=
    le_antisymm (le_of_not_gt hn) (centeredEnergy_bounds q).1
  have ha := (integral_eq_zero_iff_of_nonneg
    (fun z => div_nonneg (sq_nonneg ‖centeredSource q z‖) (positiveSource_pos z).le)
    (centered_density_integrable q)).mp he
  apply centeredSource_not_ae_zero q
  filter_upwards [ha] with z hz
  have hnum : ‖centeredSource q z‖^2=0 := by
    exact (div_eq_zero_iff.mp hz).resolve_right (positiveSource_pos z).ne'
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (centeredSource q z)]

/-- The full native energy strictly exceeds its exact mean contribution. -/
theorem nativeEnergy_lower_strict (q : XiZeroCopy) :
    sourceMass/‖xiSpectralPoint q-Complex.I‖^2 < nativeEnergy q := by
  have hp := centeredEnergy_pos q
  rw [centeredEnergy_eq] at hp
  linarith

/-- The nonzero exact Eisenstein pairing is an absolutely integrable native pairing. -/
theorem centeredSource_pairing_integrable (q : XiZeroCopy) :
    Integrable (fun z => centeredSource q z*(positiveCuspRows 2 z:ℂ)) angularMeasure := by
  by_contra hn
  exact centeredSource_pairing_ne_zero q (integral_undef hn)

/-- The original centered theta source as an actual native Hilbert vector. -/
def centeredVector (q : XiZeroCopy) : Space := (centeredSource_memLp q).toLp (centeredSource q)

theorem centeredVector_coe (q : XiZeroCopy) :
    (centeredVector q : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] centeredSource q :=
  (centeredSource_memLp q).coeFn_toLp

/-- Complete periodization preserves a nonzero centered native vector. -/
theorem centeredVector_ne_zero (q : XiZeroCopy) : centeredVector q ≠ 0 := by
  intro he
  apply centeredSource_not_ae_zero q
  have hz : (centeredVector q : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] fun _ => (0:ℂ) := by
    rw [he]
    exact Lp.coeFn_zero ℂ 2 angularMeasure
  exact (centeredVector_coe q).symm.trans hz

/-- Normalization of the complete centered theta source in the original native norm. -/
def centeredUnit (q : XiZeroCopy) : Space :=
  ((‖centeredVector q‖⁻¹:ℝ):ℂ) • centeredVector q

/-- The actual centered source normalization has native norm exactly one. -/
theorem centeredUnit_norm (q : XiZeroCopy) : ‖centeredUnit q‖=1 := by
  have hn : 0 < ‖centeredVector q‖ := norm_pos_iff.mpr (centeredVector_ne_zero q)
  rw [centeredUnit,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
  exact inv_mul_cancel₀ hn.ne'

/-- The literal native vector retains the exact zero mean of the centered source. -/
theorem centeredVector_integral (q : XiZeroCopy) :
    (∫ z, (centeredVector q : UpperHalfPlane → ℂ) z ∂angularMeasure)=0 := by
  rw [integral_congr_ae (centeredVector_coe q),centeredSource_integral]

end
end RHTower.SelbergThetaNativePairing
