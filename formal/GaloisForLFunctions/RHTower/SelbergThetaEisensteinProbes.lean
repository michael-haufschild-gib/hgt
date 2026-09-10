import GaloisForLFunctions.HTGeometry.KreinLangerInertia
import GaloisForLFunctions.RHTower.SelbergThetaCommonForcingGram
import GaloisForLFunctions.RHTower.SelbergThetaNativeMoments
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStripMeanAdmission

/-!
# Complete Eisenstein probes separate finite native theta packets

The full positive Eisenstein series at every real parameter `r > 1` defines an
absolutely admitted pairing on periodizations of rapidly decaying height seeds.
Its two Weyl terms give the seed moments at `r` and `1-r` with the original
completion ratio. For the literal reflected theta response this becomes

`integral source(q) * E_r = probeMass(r) / (alpha(q)^2 + (2r-1)^2)`,

where `probeMass(r)` is strictly positive. All source and row admission is proved
for the actual profiles, at both real and nonreal spectral energies.

Applying `A-1` to a zero packet removes its true constant component exactly.
The resulting complete Eisenstein pairings force a rational coefficient identity
at every `r > 1`. A finite family of these probes is a nonsingular Cauchy matrix
when the squared spectral parameters are distinct. Hence every nonzero coefficient
packet of distinct actual native responses has nonzero original native mass.

These pairings and finite separation do not supply a uniform cofinal norm bound
or a vanishing normalized full residual.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
namespace RHTower.SelbergThetaEisensteinProbes
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse
open SelbergThetaNativeSource SelbergThetaNativeMoments SelbergThetaCommonForcing
noncomputable section

private theorem completion_ratio (r : ℝ) (hr : 1 < r) :
    reflectedCompletedLambda (2*(r:ℂ)-1) =
      reflectedCompletedLambda (2*(r:ℂ))*(cuspReflectionNorm r:ℂ) := by
  have he := lowCuspPower_completed_mean ⟨(r:ℂ),hr⟩ 2 (by norm_num)
  simp_rw [← positiveLowCuspRows_coe r hr] at he
  rw [integral_const_mul,integral_complex_ofReal,
    positiveLowCuspRows_mean r hr (by norm_num : (2:ℝ) ≤ 2)] at he
  have hp : (2:ℂ)^(1-(r:ℂ)) = (((2:ℝ)^(1-r):ℝ):ℂ) := by
    simpa only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_ofNat]
      using (Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2) (1-r)).symm
  norm_num only [Complex.ofReal_ofNat] at he
  rw [hp] at he
  have hn : (((2:ℝ)^(1-r):ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
  apply mul_right_cancel₀ hn
  push_cast at he
  linear_combination -he

private theorem principal_power (s : ℂ) (y : ℝ) :
    principal (s-1/2) ![0,y] =
      reflectedCompletedLambda (2*s-1)*(y:ℂ)^(1-s)+
        reflectedCompletedLambda (2*s)*(y:ℂ)^s := by
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCompletedEisensteinCuspConstantMaassFactor,d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign,Bool.false_eq_true,if_false,if_true,mul_one]
  norm_num only
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  rw [show (2:ℂ)*(s-1/2)=2*s-1 by ring,
    show (1:ℂ)+(2*s-1)=2*s by ring,
    show (1/2:ℂ)+(-1)*(s-1/2)=1-s by ring,
    show (1/2:ℂ)+1*(s-1/2)=s by ring]

/-- The complete positive horocycle mean retains both original Weyl powers. -/
theorem positive_mean (r : ℝ) (hr : 1 < r) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0:ℝ) 1, positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ))) =
      y^r+cuspReflectionNorm r*y^(1-r) := by
  apply Complex.ofReal_injective
  apply mul_left_cancel₀ (cuspCompletedLambda_ne_zero (by simp; linarith : 1 < (2*(r:ℂ)).re))
  rw [positiveCuspRows_completed_mean r hr hy,principal_power,completion_ratio r hr]
  have hp : (y:ℂ)^(1-(r:ℂ)) = ((y^(1-r):ℝ):ℂ) := by
    simpa only [Complex.ofReal_sub,Complex.ofReal_one]
      using (Complex.ofReal_cpow hy.le (1-r)).symm
  rw [hp,← Complex.ofReal_cpow hy.le r]
  push_cast
  ring

private theorem positive_invariant (r : ℝ) (hr : 1 < r) (g : PSL2Z) (z : UpperHalfPlane) :
    positiveCuspRows r (g • z) = positiveCuspRows r z := by
  apply Complex.ofReal_injective
  rw [positiveCuspRows_coe r hr,positiveCuspRows_coe r hr]
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
    (hb : ∀ a : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^a)
    (r : ℝ) (hr : 1 < r) :
    IntegrableOn (fun z : UpperHalfPlane => h z.im*(positiveCuspRows r z:ℂ)) modularStrip volume := by
  have hmeas : Measurable (fun z : UpperHalfPlane => h z.im*(positiveCuspRows r z:ℂ)) :=
    (hm.comp UpperHalfPlane.continuous_im.measurable).mul
      (Complex.continuous_ofReal.measurable.comp (positiveCuspRows_measurable r))
  apply modularStrip_integrable_of_norm_mean _ hmeas
  · intro y hy
    have hi := (positiveCuspRows_horizontal_integrable r hr hy).ofReal.const_mul (h y)
    simpa only [point_im _ _ hy] using! hi
  · have hi := (profile_power_integrable h hm hb (r-2)).add
      ((profile_power_integrable h hm hb (-1-r)).const_mul (cuspReflectionNorm r))
    apply hi.congr_fun _ measurableSet_Ioi
    intro y hy
    have he : (∫ x in Ico (0:ℝ) 1,
        ‖h (ofComplex (⟨x,y⟩:ℂ)).im*(positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ)):ℂ)‖) =
        ‖h y‖*(y^r+cuspReflectionNorm r*y^(1-r)) := by
      simp only [point_im _ _ hy,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (positiveCuspRows_nonneg r _)]
      rw [integral_const_mul,positive_mean r hr hy]
    have hp1 : y^(r-2) = y^r/y^2 := by rw [Real.rpow_sub hy,Real.rpow_two]
    have hp2 : y^(-1-r) = y^(1-r)/y^2 := by
      rw [← Real.rpow_two y,← Real.rpow_sub hy]
      congr 1
      ring
    simp only [Pi.add_apply]
    rw [he,hp1,hp2]
    change ‖h y‖*(y^r/y^2)+cuspReflectionNorm r*(‖h y‖*(y^(1-r)/y^2)) = _
    ring

private theorem profile_rows_summable (h : ℝ → ℂ)
    (hb : ∀ r : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^r)
    (z : UpperHalfPlane) : Summable (fun v : gammaSetHalf => h (gammaSetMatrix v.1 • z).im) := by
  obtain ⟨C,_,hC⟩ := hb 2
  apply Summable.of_norm_bounded ((positiveCuspRows_summable 2 (by norm_num) z).mul_left C)
  intro v
  exact hC _ (gammaSetMatrix v.1 • z).im_pos

private theorem product_unfold (h : ℝ → ℂ) (hm : Measurable h)
    (hb : ∀ a : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^a)
    (r : ℝ) (hr : 1 < r) :
    Integrable (fun z => periodize (cuspHeightSeed h) z*(positiveCuspRows r z:ℂ)) angularMeasure ∧
      (∫ z, periodize (cuspHeightSeed h) z*(positiveCuspRows r z:ℂ) ∂angularMeasure) =
        ∫ z in modularStrip, h z.im*(positiveCuspRows r z:ℂ) := by
  let φ : UpperHalfPlane → ℂ := fun z => h z.im*(positiveCuspRows r z:ℂ)
  have hφ : IntegrableOn φ modularStrip volume := product_strip_integrable h hm hb r hr
  have hp (n : ℤ) (z : UpperHalfPlane) : φ (ModularGroup.T^n • z)=φ z := by
    change h (ModularGroup.T^n • z).im*(positiveCuspRows r (ModularGroup.T^n • z):ℂ) =
      h z.im*(positiveCuspRows r z:ℂ)
    rw [im_T_zpow_smul]
    have he := positive_invariant r hr (QuotientGroup.mk (ModularGroup.T^n):PSL2Z) z
    simpa only [PSL2Z_mk_smul] using congrArg (fun t : ℝ => h z.im*(t:ℂ)) he
  have htranslate (v : gammaSetHalf) (z : UpperHalfPlane) :
      φ (gammaSetMatrix v.1 • z)=h (gammaSetMatrix v.1 • z).im*(positiveCuspRows r z:ℂ) := by
    change h (gammaSetMatrix v.1 • z).im*(positiveCuspRows r (gammaSetMatrix v.1 • z):ℂ) =
      h (gammaSetMatrix v.1 • z).im*(positiveCuspRows r z:ℂ)
    have he := positive_invariant r hr (QuotientGroup.mk (gammaSetMatrix v.1):PSL2Z) z
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
  have he : (fun z => periodize (cuspHeightSeed h) z*(positiveCuspRows r z:ℂ)) =
      (fun z => ∑' v : gammaSetHalf, φ (gammaSetMatrix v.1 • z)) := by
    funext z
    simp_rw [htranslate]
    rw [tsum_mul_right,periodize_cuspHeightSeed_eq_rows_of_rows_summable h z
      (profile_rows_summable h hb z)]
  constructor
  · rw [he]
    exact integrable_tsum_of_summable_integral_norm hrow hsum
  · change (∫ z, (fun z => periodize (cuspHeightSeed h) z*(positiveCuspRows r z:ℂ)) z
        ∂angularMeasure) = _
    rw [he]
    exact ht.symm.trans hu

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


/-- Absolute admission of the full primitive-row pairing for every positive Eisenstein parameter. -/
theorem profile_eisenstein_integrable (h : ℝ → ℂ) (hm : Measurable h)
    (hb : ∀ a : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^a)
    (r : ℝ) (hr : 1 < r) :
    Integrable (fun z => periodize (cuspHeightSeed h) z*(positiveCuspRows r z:ℂ)) angularMeasure :=
  (product_unfold h hm hb r hr).1

/-- Exact two-Weyl Mellin pairing for a rapidly decaying height profile. -/
theorem profile_eisenstein_pairing (h : ℝ → ℂ) (hm : Measurable h)
    (hb : ∀ a : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖h y‖ ≤ C*y^a)
    (r : ℝ) (hr : 1 < r) :
    (∫ z, periodize (cuspHeightSeed h) z*(positiveCuspRows r z:ℂ) ∂angularMeasure) =
      (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^r:ℝ)))+
        (cuspReflectionNorm r:ℂ)*(∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^(1-r):ℝ))) := by
  rw [(product_unfold h hm hb r hr).2,
    setIntegral_modularStrip_eq_iterated _ (product_strip_integrable h hm hb r hr)]
  have he : (∫ y in Ioi (0:ℝ), (y^2)⁻¹ •
      ∫ x in Ico (0:ℝ) 1,
        h (ofComplex (⟨x,y⟩:ℂ)).im*(positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ)):ℂ)) =
      ∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^r:ℝ))+
        (cuspReflectionNorm r:ℂ)*((y^2)⁻¹ • (h y*(y^(1-r):ℝ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [point_im _ _ hy]
    rw [integral_const_mul,integral_complex_ofReal,positive_mean r hr hy]
    simp only [Complex.real_smul,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  rw [he]
  have hs : (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^r:ℝ))+
      (cuspReflectionNorm r:ℂ)*((y^2)⁻¹ • (h y*(y^(1-r):ℝ)))) =
      (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (h y*(y^r:ℝ)))+
        (∫ y in Ioi (0:ℝ), (cuspReflectionNorm r:ℂ)*((y^2)⁻¹ • (h y*(y^(1-r):ℝ)))) := by
    simpa using! integral_add (profile_mellin_integrable h hm hb r)
      ((profile_mellin_integrable h hm hb (1-r)).const_mul (cuspReflectionNorm r:ℂ))
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

private theorem heightProfile_measurable (q : XiZeroCopy) : Measurable (heightProfile q) := by
  have hp := (profile_contDiff q).continuous.measurable
  unfold heightProfile
  exact (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.div_const 2).exp).mul
    (hp.comp (Real.measurable_log.div_const 2))

private theorem spectral_re_ne_zero (q : XiZeroCopy) : (xiSpectralPoint q).re ≠ 0 := by
  simpa [xiSpectralPoint,Complex.mul_re,Complex.mul_im] using xi_divisor_support_im_ne_zero q.1

private theorem shift_ne_zero (q : XiZeroCopy) (a : ℝ) :
    xiSpectralPoint q+Complex.I*(a:ℂ) ≠ 0 := by
  intro he
  apply spectral_re_ne_zero q
  have hr := congrArg Complex.re he
  simpa using hr

/-- Every real Mellin probe avoids the spectral denominator of an actual Xi copy. -/
theorem real_probe_denominator_ne_zero (q : XiZeroCopy) (a : ℝ) :
    (xiSpectralPoint q)^2+(a:ℂ)^2 ≠ 0 := by
  have hm : xiSpectralPoint q-Complex.I*(a:ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg,mul_neg,← sub_eq_add_neg] using shift_ne_zero q (-a)
  have he : (xiSpectralPoint q+Complex.I*(a:ℂ))*(xiSpectralPoint q-Complex.I*(a:ℂ)) =
      (xiSpectralPoint q)^2+(a:ℂ)^2 := by
    linear_combination -(a:ℂ)^2*I_sq
  rw [← he]
  exact mul_ne_zero (shift_ne_zero q a) hm

/-- All real Mellin moments of the literal reflected common-forcing height profile. -/
theorem heightProfile_mellin (q : XiZeroCopy) (r : ℝ) :
    (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (heightProfile q y*(y^r:ℝ))) =
      (tiltedMass (2*r-1):ℂ)/((xiSpectralPoint q)^2+((2*r-1:ℝ):ℂ)^2) := by
  have he (y : ℝ) : (y^2)⁻¹ • (heightProfile q y*(y^r:ℝ)) =
      -((y^2)⁻¹ • (modeProfile q y*(y^r:ℝ))-
        (y^2)⁻¹ • (modeProfile (xiZeroCopyReflectEquiv q) y*(y^r:ℝ)))/(2*xiSpectralPoint q) := by
    rw [heightProfile_eq_pair]
    simp only [Complex.real_smul]
    ring
  simp_rw [he]
  have hq := profile_mellin_integrable (modeProfile q) (modeProfile_measurable q)
    (modeProfile_power_bound q) r
  have href := profile_mellin_integrable (modeProfile (xiZeroCopyReflectEquiv q))
    (modeProfile_measurable _) (modeProfile_power_bound _) r
  rw [integral_div,integral_neg,integral_sub hq href,
    modeProfile_mellin,modeProfile_mellin,xiSpectralPoint_reflect]
  have h0 : xiSpectralPoint q ≠ 0 := by
    intro h
    exact spectral_re_ne_zero q (by rw [h]; rfl)
  have h1 := shift_ne_zero q (2*r-1)
  have h2 := shift_ne_zero (xiZeroCopyReflectEquiv q) (2*r-1)
  rw [xiSpectralPoint_reflect] at h2
  have hd := real_probe_denominator_ne_zero q (2*r-1)
  field_simp
  linear_combination -(tiltedMass (2*r-1):ℂ)*((2*r-1:ℝ):ℂ)^2*(xiSpectralPoint q)*I_sq*2

/-- The positive theta-source mass seen by the complete Eisenstein probe. -/
def probeMass (r : ℝ) : ℝ := (1+cuspReflectionNorm r)*tiltedMass (2*r-1)

theorem probeMass_pos (r : ℝ) : 0 < probeMass r :=
  mul_pos (by linarith [cuspReflectionNorm_nonneg r]) (tiltedMass_pos _)

private theorem positiveSource_periodize (z : UpperHalfPlane) :
    (positiveSource z:ℂ) = periodize (cuspHeightSeed (fun y => (positiveProfile y:ℂ))) z := by
  have hs := profile_rows_summable (fun y : ℝ => (positiveProfile y:ℂ))
    positiveProfile_norm_bounds z
  have hh := periodize_cuspHeightSeed_eq_rows_of_rows_summable
    (fun y : ℝ => (positiveProfile y:ℂ)) z hs
  exact (Complex.ofReal_tsum (fun v : gammaSetHalf =>
    positiveProfile (gammaSetMatrix v.1 • z).im)).trans hh.symm

/-- Absolute admission for the original full positive theta source. -/
theorem positiveSource_eisenstein_integrable (r : ℝ) (hr : 1 < r) :
    Integrable (fun z => (positiveSource z:ℂ)*(positiveCuspRows r z:ℂ)) angularMeasure := by
  simp_rw [positiveSource_periodize]
  exact profile_eisenstein_integrable _
    (Complex.continuous_ofReal.measurable.comp positiveProfile_measurable)
    positiveProfile_norm_bounds r hr

/-- The complete positive theta source has exactly the stated positive probe mass. -/
theorem positiveSource_eisenstein_pairing (r : ℝ) (hr : 1 < r) :
    (∫ z, (positiveSource z:ℂ)*(positiveCuspRows r z:ℂ) ∂angularMeasure) = (probeMass r:ℂ) := by
  simp_rw [positiveSource_periodize]
  rw [profile_eisenstein_pairing (fun y : ℝ => (positiveProfile y:ℂ))
    (Complex.continuous_ofReal.measurable.comp positiveProfile_measurable)
    positiveProfile_norm_bounds r hr,positiveProfile_mellin,positiveProfile_mellin,
    show 2*(1-r)-1 = -(2*r-1) by ring,tiltedMass_neg]
  unfold probeMass
  push_cast
  ring

/-- Absolute admission for every actual reflected source, with all native rows retained. -/
theorem source_eisenstein_integrable (q : XiZeroCopy) (r : ℝ) (hr : 1 < r) :
    Integrable (fun z => source q z*(positiveCuspRows r z:ℂ)) angularMeasure := by
  simp_rw [source_eq_periodize]
  exact profile_eisenstein_integrable _ (heightProfile_measurable q)
    (heightProfile_power_bound q) r hr

/-- The full arithmetic Eisenstein pairing of every actual common-forcing response. -/
theorem source_eisenstein_pairing (q : XiZeroCopy) (r : ℝ) (hr : 1 < r) :
    (∫ z, source q z*(positiveCuspRows r z:ℂ) ∂angularMeasure) =
      (probeMass r:ℂ)/((xiSpectralPoint q)^2+((2*r-1:ℝ):ℂ)^2) := by
  simp_rw [source_eq_periodize]
  rw [profile_eisenstein_pairing _ (heightProfile_measurable q)
    (heightProfile_power_bound q) r hr,heightProfile_mellin,heightProfile_mellin,
    show 2*(1-r)-1 = -(2*r-1) by ring,tiltedMass_neg]
  simp only [Complex.ofReal_neg,neg_sq]
  unfold probeMass
  push_cast
  ring

open SelbergThetaCommonForcingGram SelbergNativeConstantMode

private def descendedVector (q : XiZeroCopy) : Space :=
  (energy q-1) • nativeSource q-(1/4:ℂ) • nativePositive

private def descendedField (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  (energy q-1)*source q z-(positiveSource z:ℂ)/4

/-- Subtracting the identity removes the true constant component of the native operator image. -/
theorem image_sub_vector (q : XiZeroCopy) :
    image q-vector q = (energy q-1) • nativeSource q-(1/4:ℂ) • nativePositive := by
  unfold SelbergThetaCommonForcingGram.image vector centeredDomain
  rw [energyOperator.map_sub,energyOperator.map_smul,constantEnergyDomain_operator,nativeDomain_image]
  change (energy q • nativeSource q-(1/4:ℂ) • nativePositive)-_ • constantVector-
    (nativeSource q-_ • constantVector) = _
  module

private theorem descendedVector_coe (q : XiZeroCopy) :
    (descendedVector q : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] descendedField q := by
  have hq : (nativeSource q : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] source q :=
    (source_memLp q).coeFn_toLp
  have hP : (nativePositive : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
      (fun z => (positiveSource z:ℂ)) := positiveSource_memLp.ofReal.coeFn_toLp
  filter_upwards [Lp.coeFn_sub ((energy q-1) • nativeSource q) ((1/4:ℂ) • nativePositive),
    Lp.coeFn_smul (energy q-1) (nativeSource q),Lp.coeFn_smul (1/4:ℂ) nativePositive,hq,hP]
    with z hs h1 h2 hq hP
  change (((energy q-1) • nativeSource q-(1/4:ℂ) • nativePositive):Space) z = _
  simp only [Pi.sub_apply] at hs
  simp only [Pi.smul_apply,smul_eq_mul] at h1 h2
  rw [hs,h1,h2,hq,hP]
  unfold descendedField
  ring

private theorem descendedField_eisenstein_integrable (q : XiZeroCopy) (r : ℝ) (hr : 1 < r) :
    Integrable (fun z => descendedField q z*(positiveCuspRows r z:ℂ)) angularMeasure := by
  have h := ((source_eisenstein_integrable q r hr).const_mul (energy q-1)).sub
    ((positiveSource_eisenstein_integrable r hr).div_const 4)
  apply h.congr
  exact Eventually.of_forall fun z => by dsimp [descendedField]; ring

private theorem descendedField_eisenstein_pairing (q : XiZeroCopy) (r : ℝ) (hr : 1 < r) :
    (∫ z, descendedField q z*(positiveCuspRows r z:ℂ) ∂angularMeasure) =
      ((1-((2*r-1:ℝ):ℂ)^2)/4*(probeMass r:ℂ))/
        ((xiSpectralPoint q)^2+((2*r-1:ℝ):ℂ)^2) := by
  have he (z : UpperHalfPlane) : descendedField q z*(positiveCuspRows r z:ℂ) =
      (energy q-1)*(source q z*(positiveCuspRows r z:ℂ))-
        ((positiveSource z:ℂ)*(positiveCuspRows r z:ℂ))/4 := by
    unfold descendedField
    ring
  simp_rw [he]
  rw [integral_sub ((source_eisenstein_integrable q r hr).const_mul _)
    ((positiveSource_eisenstein_integrable r hr).div_const 4),integral_const_mul,integral_div,
    source_eisenstein_pairing q r hr,positiveSource_eisenstein_pairing r hr]
  apply (eq_div_iff (real_probe_denominator_ne_zero q (2*r-1))).2
  rw [sub_mul,mul_assoc,div_mul_cancel₀ _ (real_probe_denominator_ne_zero q (2*r-1))]
  unfold energy
  ring

private theorem descended_packet_zero {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ)
    (hv : (∑ i, c i • vector (q i)) = 0) : (∑ i, c i • descendedVector (q i)) = 0 := by
  have hd : packetDomain q c = 0 :=
    Subtype.ext (by simpa only [packetDomain_coe,Submodule.coe_zero] using hv)
  have h := packetDomain_residual q c 1
  rw [hd,energyOperator.map_zero] at h
  simp only [Submodule.coe_zero,smul_zero,sub_self] at h
  simpa only [SelbergThetaCommonForcingGram.residual,one_smul,image_sub_vector,descendedVector] using h.symm


private theorem descended_field_packet_zero {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ)
    (hv : (∑ i, c i • vector (q i)) = 0) :
    (fun z => ∑ i, c i*descendedField (q i) z) =ᵐ[angularMeasure] 0 := by
  have ht (i : ι) : ((c i • descendedVector (q i):Space) : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
      (fun z => c i*descendedField (q i) z) := by
    filter_upwards [Lp.coeFn_smul (c i) (descendedVector (q i)),descendedVector_coe (q i)]
      with z hc hd
    simpa only [Pi.smul_apply,smul_eq_mul,hd] using hc
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • descendedVector (q i))
  rw [descended_packet_zero q c hv] at hsum
  filter_upwards [hsum,ae_all_iff.mpr ht,Lp.coeFn_zero ℂ 2 angularMeasure] with z hs ht hz
  change (∑ i, c i*descendedField (q i) z) = 0
  have he : (∑ i, (c i • descendedVector (q i):Space) z) =
      ∑ i, c i*descendedField (q i) z := Finset.sum_congr rfl (fun i _ => ht i)
  rw [he,hz] at hs
  exact hs.symm

/-- A zero native packet has zero rational readout at every positive Eisenstein probe. -/
theorem packet_zero_probe_identity {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ)
    (hv : (∑ i, c i • vector (q i)) = 0) (r : ℝ) (hr : 1 < r) :
    ∑ i, c i/((xiSpectralPoint (q i))^2+((2*r-1:ℝ):ℂ)^2) = 0 := by
  have hae := descended_field_packet_zero q c hv
  have hInt : (∫ z, ∑ i, c i*(descendedField (q i) z*(positiveCuspRows r z:ℂ))
      ∂angularMeasure) = 0 := by
    have he : (fun z => ∑ i, c i*(descendedField (q i) z*(positiveCuspRows r z:ℂ))) =ᵐ[angularMeasure]
        (fun _ => (0:ℂ)) := by
      filter_upwards [hae] with z hz
      simp only [← mul_assoc,← Finset.sum_mul,hz,Pi.zero_apply,zero_mul]
    rw [integral_congr_ae he,integral_zero]
  rw [integral_finsetSum _ (fun i _ =>
    (descendedField_eisenstein_integrable (q i) r hr).const_mul (c i))] at hInt
  simp_rw [integral_const_mul,descendedField_eisenstein_pairing _ r hr] at hInt
  have he : (∑ i, c i*(((1-((2*r-1:ℝ):ℂ)^2)/4*(probeMass r:ℂ))/
      ((xiSpectralPoint (q i))^2+((2*r-1:ℝ):ℂ)^2))) =
      ((1-((2*r-1:ℝ):ℂ)^2)/4*(probeMass r:ℂ))*
        (∑ i, c i/((xiSpectralPoint (q i))^2+((2*r-1:ℝ):ℂ)^2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hInt
  have hreal : (1-(2*r-1)^2:ℝ) ≠ 0 := by nlinarith
  have hcomplex : (1-((2*r-1:ℝ):ℂ)^2) ≠ 0 := by exact_mod_cast hreal
  exact (mul_eq_zero.mp hInt).resolve_left
    (mul_ne_zero (div_ne_zero hcomplex (by norm_num))
      (Complex.ofReal_ne_zero.mpr (probeMass_pos r).ne'))

/-- Every finite family of actual centered responses with distinct native energies is
linearly independent, including energies on the real axis. -/
theorem vector_linearIndependent {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy)
    (hq : Function.Injective (fun i => (xiSpectralPoint (q i))^2)) :
    LinearIndependent ℂ (fun i => vector (q i)) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let r : ι → ℝ := fun i => ((e i).val:ℝ)+2
  have hr (i : ι) : 1 < r i := by
    dsimp [r]
    linarith [Nat.cast_nonneg (α := ℝ) (e i).val]
  let node : ι → ℂ := fun i => -((2*r i-1:ℝ):ℂ)^2
  have hn : Function.Injective node := by
    intro i j hij
    have he := congrArg Complex.re hij
    have hsq : (2*r i-1)^2 = (2*r j-1)^2 := by
      simpa only [node,Complex.neg_re,← Complex.ofReal_pow,Complex.ofReal_re,neg_inj] using he
    have heq : r i = r j := by nlinarith [hr i,hr j]
    apply e.injective
    apply Fin.ext
    have hv : ((e i).val:ℝ) = ((e j).val:ℝ) := by dsimp [r] at heq; linarith
    exact_mod_cast hv
  have hp : ∀ i j, (xiSpectralPoint (q i))^2 ≠ node j := by
    intro i j h
    have hd := real_probe_denominator_ne_zero (q i) (2*r j-1)
    apply hd
    change (xiSpectralPoint (q i))^2 = -((2*r j-1:ℝ):ℂ)^2 at h
    rw [h,neg_add_cancel]
  have hLI := GaloisForLFunctions.cauchy_linearIndependent
    (fun i => (xiSpectralPoint (q i))^2) node hq hn hp
  rw [Fintype.linearIndependent_iff] at hLI ⊢
  intro c hc i
  apply hLI c _ i
  funext j
  have he := packet_zero_probe_identity q c hc (r j) (hr j)
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,node,
    sub_neg_eq_add,div_eq_mul_inv] using he

/-- Every nonzero finite coefficient packet at distinct actual native energies retains mass. -/
theorem packet_ne_zero {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ)
    (hq : Function.Injective (fun i => (xiSpectralPoint (q i))^2))
    (hc : c ≠ 0) : (∑ i, c i • vector (q i)) ≠ 0 := by
  intro hv
  apply hc
  funext i
  exact (Fintype.linearIndependent_iff.mp (vector_linearIndependent q hq)) c hv i

end
end RHTower.SelbergThetaEisensteinProbes
