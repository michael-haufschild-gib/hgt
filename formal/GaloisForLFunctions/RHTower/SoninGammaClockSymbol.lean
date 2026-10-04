import GaloisForLFunctions.RHTower.SoninGammaClockEndpoint
import Mathlib.Analysis.Calculus.ParametricIntegral
import GaloisForLFunctions.RHTower.DigammaIntegralRepresentation
import GaloisForLFunctions.RHTower.GammaXiResponseGapOneCutSpectrum

/-!
# The exact Gamma logarithmic-clock symbol

The literal Gamma sine source is the imaginary Gauss digamma integral with
its physical-clock normalization. One integrable envelope permits differentiation
of the full clock-divided cosine primitive. Its derivative and value at zero
identify it with twice the normalized quarter-line Gamma log modulus.

This is the scalar source identity. Functional calculus on the Sonin carrier,
the principal reference domain, and the Hardy/sub-unit passage remain separate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem gammaGauss_sine (ξ u : ℝ) (hu : 0 < u) :
    (digammaGaussIntegrand (1/4+((ξ/2:ℝ):ℂ)*Complex.I) (2*u)).im =
      Real.sin (ξ*u)*ccmPublishedArchimedeanDensity u := by
  rw [digammaGaussIntegrand, Complex.sub_im, Complex.ofReal_im,
    one_sub_exp_neg_ofReal_eq, Complex.div_ofReal_im, Complex.exp_im]
  have hre : (-(1/4+((ξ/2:ℝ):ℂ)*Complex.I)*((2*u:ℝ):ℂ)).re = -u/2 := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have him : (-(1/4+((ξ/2:ℝ):ℂ)*Complex.I)*((2*u:ℝ):ℂ)).im = -(ξ*u) := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [hre, him, Real.sin_neg, ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hu]
  ring

/-- Exact full Gamma sine integrability, with its literal physical-clock density. -/
theorem gammaClockSine_integrable (ξ : ℝ) :
    IntegrableOn (fun u => Real.sin (ξ*u)*ccmPublishedArchimedeanDensity u) (Ioi 0) := by
  let z : ℂ := 1/4+((ξ/2:ℝ):ℂ)*Complex.I
  have hz : 0 < z.re := by simp [z]
  have hi := Complex.imCLM.integrable_comp (integrableOn_digammaGaussIntegrand hz)
  have hs : IntegrableOn (fun u => (digammaGaussIntegrand z (2*u)).im) (Ioi (0:ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun u => (digammaGaussIntegrand z u).im) 0 (show (0:ℝ)<2 by norm_num)).mpr
    simpa only [mul_zero, Complex.imCLM_apply] using! hi
  exact hs.congr_fun (fun u hu => gammaGauss_sine ξ u hu) measurableSet_Ioi

/-- The literal odd Gamma source equals the imaginary digamma value, including normalization. -/
theorem integral_gammaClockSine (ξ : ℝ) :
    (∫ u in Ioi (0:ℝ), Real.sin (ξ*u)*ccmPublishedArchimedeanDensity u) =
      (1/2)*(Complex.digamma (1/4+((ξ/2:ℝ):ℂ)*Complex.I)).im := by
  let z : ℂ := 1/4+((ξ/2:ℝ):ℂ)*Complex.I
  have hz : 0 < z.re := by simp [z]
  have hc := Complex.imCLM.integral_comp_comm (integrableOn_digammaGaussIntegrand hz)
  simp only [Complex.imCLM_apply] at hc
  calc
    _ = ∫ u in Ioi (0:ℝ), (digammaGaussIntegrand z (2*u)).im :=
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => (gammaGauss_sine ξ u hu).symm)
    _ = (1/2)*(∫ u in Ioi (0:ℝ), (digammaGaussIntegrand z u).im) := by
      simpa only [mul_zero, smul_eq_mul, one_div] using
        integral_comp_mul_left_Ioi (fun u => (digammaGaussIntegrand z u).im) 0
          (show (0:ℝ)<2 by norm_num)
    _ = _ := by rw [hc, ← digamma_eq_integral_gauss hz]

/-- The full Gamma sine source is the negative derivative of the normalized Gamma log modulus. -/
theorem hasDerivAt_gammaClockLogModulus (ξ : ℝ) :
    HasDerivAt
      (fun t : ℝ => 2*(Real.log ‖Complex.Gamma (1/4+((t/2:ℝ):ℂ)*Complex.I)‖-
        Real.log ‖Complex.Gamma (1/4)‖))
      (-2*∫ u in Ioi (0:ℝ), Real.sin (ξ*u)*ccmPublishedArchimedeanDensity u) ξ := by
  have h := ((hasDerivAt_log_norm_Gamma_vertical (a := (1/4:ℝ)) (t := ξ/2)
    (by norm_num)).comp ξ ((hasDerivAt_id ξ).div_const 2)).sub_const
      (Real.log ‖Complex.Gamma (1/4)‖)
  have hh := h.const_mul 2
  rw [integral_gammaClockSine]
  convert! hh using 1 <;> norm_num
  ring

private def gammaClockSourceEnvelope (u : ℝ) : ℝ :=
  if u ≤ 1/2 then u*ccmPublishedArchimedeanDensity u else ccmPublishedArchimedeanDensity u

private theorem gammaClock_density_pos {u : ℝ} (hu : 0 < u) :
    0 < ccmPublishedArchimedeanDensity u := by
  rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hu]
  exact div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))

private theorem gammaClock_density_tail {u : ℝ} (hu : 1/2 ≤ u) :
    ccmPublishedArchimedeanDensity u ≤ (1/(1-Real.exp (-1)))*Real.exp (-u/2) := by
  have hu0 : 0 < u := by linarith
  have hd : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hu0]
  have hm : 1-Real.exp (-1) ≤ 1-Real.exp (-2*u) := by
    have hh := Real.exp_le_exp.mpr (show -2*u ≤ -1 by linarith)
    linarith
  calc
    _ ≤ Real.exp (-u/2)/(1-Real.exp (-1)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hd hm
    _ = _ := by ring

private theorem gammaClock_firstMoment_near_zero {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1/2) :
    u*ccmPublishedArchimedeanDensity u ≤ 2 := by
  have h := (le_abs_self (gammaClockRemainderDensity u)).trans
    (gammaClockRemainderDensity_near_zero hu hu1)
  have hd : gammaClockRemainderDensity u*u^2 = u*ccmPublishedArchimedeanDensity u-1/2 := by
    unfold gammaClockRemainderDensity
    field_simp
  have hh := mul_le_mul_of_nonneg_right h (sq_nonneg u)
  rw [hd] at hh
  have hr : ((5/2)/u)*u^2 = (5/2)*u := by field_simp
  rw [hr] at hh
  linarith

private theorem gammaClock_envelope_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ gammaClockSourceEnvelope u := by
  have hg := gammaClock_density_pos hu
  unfold gammaClockSourceEnvelope
  split_ifs <;> positivity

private theorem gammaClock_envelope_measurable : Measurable gammaClockSourceEnvelope := by
  have hg : Measurable ccmPublishedArchimedeanDensity := by
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  exact (measurable_id.mul hg).piecewise measurableSet_Iic hg

private theorem gammaClock_envelope_integrable : IntegrableOn gammaClockSourceEnvelope (Ioi 0) := by
  have hm : AEStronglyMeasurable gammaClockSourceEnvelope volume :=
    gammaClock_envelope_measurable.stronglyMeasurable.aestronglyMeasurable
  have hz : IntegrableOn gammaClockSourceEnvelope (Ioo (0:ℝ) (1/2)) := by
    have hi : IntegrableOn (fun _ : ℝ => (2:ℝ)) (Ioo (0:ℝ) (1/2)) :=
      (continuous_const.integrableOn_Icc :
        IntegrableOn (fun _ : ℝ => (2:ℝ)) (Icc (0:ℝ) (1/2))).mono_set Ioo_subset_Icc_self
    apply hi.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (gammaClock_envelope_nonneg hu.1)]
    simpa only [gammaClockSourceEnvelope, if_pos hu.2.le] using
      gammaClock_firstMoment_near_zero hu.1 hu.2.le
  have ht : IntegrableOn gammaClockSourceEnvelope (Ioi (1/2:ℝ)) := by
    have hi := (integrableOn_exp_mul_Ioi (a := -(1/2:ℝ)) (by norm_num) (1/2)).const_mul
      (1/(1-Real.exp (-1)))
    apply hi.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans (by norm_num : (0:ℝ)<1/2) hu
    rw [Real.norm_eq_abs, abs_of_nonneg (gammaClock_envelope_nonneg hu0),
      gammaClockSourceEnvelope, if_neg (not_le.mpr hu)]
    convert gammaClock_density_tail hu.le using 1
    ring
  have hu := hz.union ((integrableOn_Ici_iff_integrableOn_Ioi).mpr ht)
  have hs : Ioo (0:ℝ) (1/2) ∪ Ici (1/2) = Ioi 0 := by
    ext u
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (h|h) <;> linarith
    · intro h
      by_cases ht : u < 1/2
      · exact Or.inl ⟨h,ht⟩
      · exact Or.inr (le_of_not_gt ht)
  rwa [hs] at hu

private theorem gammaClock_cosine_quadratic (x : ℝ) : |Real.cos x-1| ≤ x^2/2 := by
  have hc := Real.cos_two_mul_eq_one_sub (x/2)
  rw [show 2*(x/2)=x by ring] at hc
  rw [hc, show 1-2*Real.sin (x/2)^2-1 = -(2*Real.sin (x/2)^2) by ring,
    abs_neg, abs_of_nonneg (by positivity)]
  nlinarith [Real.sin_sq_le_sq (x := x/2)]

/-- The exact scalar multiplier of the clock-divided symmetric Gamma kernel. -/
def gammaClockSymbol (ξ : ℝ) : ℝ :=
  ∫ u in Ioi 0, 2*(Real.cos (ξ*u)-1)*ccmPublishedArchimedeanDensity u/u

/-- Absolute integrability of the complete, zero-normalized Gamma cosine multiplier. -/
theorem gammaClockSymbol_integrable (ξ : ℝ) :
    IntegrableOn (fun u => 2*(Real.cos (ξ*u)-1)*ccmPublishedArchimedeanDensity u/u) (Ioi 0) := by
  have hm : AEStronglyMeasurable
      (fun u => 2*(Real.cos (ξ*u)-1)*ccmPublishedArchimedeanDensity u/u) volume := by
    apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  apply (gammaClock_envelope_integrable.const_mul (ξ^2+8)).mono' hm.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hu
  have hg := gammaClock_density_pos hu0
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ)≤2), abs_of_pos (gammaClock_density_pos hu0), abs_of_pos hu0]
  by_cases hsmall : u ≤ 1/2
  · rw [gammaClockSourceEnvelope, if_pos hsmall]
    calc
      _ ≤ (2*((ξ*u)^2/2)*ccmPublishedArchimedeanDensity u)/u := by
        gcongr
        exact gammaClock_cosine_quadratic (ξ*u)
      _ = ξ^2*(u*ccmPublishedArchimedeanDensity u) := by field_simp
      _ ≤ _ := by nlinarith [mul_pos hu0 (gammaClock_density_pos hu0)]
  · rw [gammaClockSourceEnvelope, if_neg hsmall]
    have hcos : |Real.cos (ξ*u)-1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [Real.neg_one_le_cos (ξ*u), Real.cos_le_one (ξ*u)]
    have huhalf : 1/2 < u := lt_of_not_ge hsmall
    have hg := gammaClock_density_pos hu0
    calc
      _ ≤ (2*2*ccmPublishedArchimedeanDensity u)/u := by gcongr
      _ ≤ (2*2*ccmPublishedArchimedeanDensity u)/(1/2) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) huhalf.le
      _ ≤ _ := by nlinarith [gammaClock_density_pos hu0, sq_nonneg ξ]

private theorem gammaClock_derivative_bound (C t u : ℝ) (hC : 1 ≤ C)
    (ht : |t| ≤ C) (hu : 0 < u) :
    ‖-2*Real.sin (t*u)*ccmPublishedArchimedeanDensity u‖ ≤
      (2*C)*gammaClockSourceEnvelope u := by
  have hg := gammaClock_density_pos hu
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hg]
  norm_num only [abs_neg]
  by_cases hs : u ≤ 1/2
  · rw [gammaClockSourceEnvelope, if_pos hs]
    have hsin : |Real.sin (t*u)| ≤ C*u := by
      calc
        _ ≤ |t*u| := Real.abs_sin_le_abs
        _ = |t| * u := by rw [abs_mul, abs_of_pos hu]
        _ ≤ C*u := mul_le_mul_of_nonneg_right ht hu.le
    nlinarith [mul_le_mul_of_nonneg_right hsin hg.le]
  · rw [gammaClockSourceEnvelope, if_neg hs]
    have hsin := Real.abs_sin_le_one (t*u)
    nlinarith [mul_le_mul_of_nonneg_right hsin hg.le]

/-- Differentiation of the full clock-divided Gamma multiplier preserves the actual sine source. -/
theorem hasDerivAt_gammaClockSymbol (ξ : ℝ) :
    HasDerivAt gammaClockSymbol
      (-2*∫ u in Ioi (0:ℝ), Real.sin (ξ*u)*ccmPublishedArchimedeanDensity u) ξ := by
  let C : ℝ := |ξ|+1
  have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg ξ]
  have hs : Ioo (-C) C ∈ 𝓝 ξ := Ioo_mem_nhds
    (by dsimp [C]; linarith [neg_abs_le ξ]) (by dsimp [C]; linarith [le_abs_self ξ])
  have hm (x : ℝ) : AEStronglyMeasurable
      (fun u => 2*(Real.cos (x*u)-1)*ccmPublishedArchimedeanDensity u/u) volume := by
    apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  have hm' : AEStronglyMeasurable
      (fun u => -2*Real.sin (ξ*u)*ccmPublishedArchimedeanDensity u) volume := by
    apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun x u : ℝ => 2*(Real.cos (x*u)-1)*ccmPublishedArchimedeanDensity u/u)
    (F' := fun x u : ℝ => -2*Real.sin (x*u)*ccmPublishedArchimedeanDensity u)
    (bound := fun u => (2*C)*gammaClockSourceEnvelope u) hs
    (Eventually.of_forall fun x => (hm x).restrict)
    (gammaClockSymbol_integrable ξ) hm'.restrict
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro x hx
      exact gammaClock_derivative_bound C x u hC (abs_le.mpr ⟨hx.1.le,hx.2.le⟩) hu)
    (gammaClock_envelope_integrable.const_mul (2*C))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro x _
      have hu0 : u ≠ 0 := ne_of_gt hu
      have hc := (((Real.hasDerivAt_cos (x*u)).comp x
        ((hasDerivAt_id x).mul_const u)).sub_const 1).const_mul 2
      have hh := (hc.mul_const (ccmPublishedArchimedeanDensity u)).div_const u
      convert! hh using 1
      field_simp)
  apply hd.2.congr_deriv
  rw [← integral_const_mul]
  congr 1
  funext u
  ring

/-- Exact Gamma source weld for every real frequency, with normalization fixed at zero. -/
theorem gammaClockSymbol_eq_log_Gamma (ξ : ℝ) :
    gammaClockSymbol ξ =
      2*(Real.log ‖Complex.Gamma (1/4+((ξ/2:ℝ):ℂ)*Complex.I)‖-
        Real.log ‖Complex.Gamma (1/4)‖) := by
  let G := fun t : ℝ => 2*(Real.log ‖Complex.Gamma (1/4+((t/2:ℝ):ℂ)*Complex.I)‖-
    Real.log ‖Complex.Gamma (1/4)‖)
  have hd (t : ℝ) : HasDerivAt (fun s => gammaClockSymbol s-G s) 0 t := by
    have h := (hasDerivAt_gammaClockSymbol t).sub (hasDerivAt_gammaClockLogModulus t)
    simpa only [sub_self] using! h
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) ξ 0
  have hz : gammaClockSymbol 0-G 0 = 0 := by simp [gammaClockSymbol,G]
  rw [hz] at hc
  exact sub_eq_zero.mp hc

end RHTower
