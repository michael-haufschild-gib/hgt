import GaloisForLFunctions.RHTower.BurnolSoninEvenCosineAperture
import GaloisForLFunctions.HyperbolicArakelovTheory.TheSobolevErrorOfTheHyperbolicGreenDamping
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicAndWeilFormDomainsAgree
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilActualHeadCompletedErrorProducer
import GaloisForLFunctions.RHTower.PoleVanishingWeilTraceCertificate
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine

/-!
# Green damping detects the complete Weil form domain

The damped hyperbolic jump energies converge for every complex aperture L²
state in the extended half-line. A finite limit occurs exactly on the complete
Weil form domain; its value plus physical mass is the form norm squared.
Adding the literal polar and saturated prime terms recovers the closed Weil
form on its whole domain and diverges outside it.
-/

set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.HyperbolicArakelovTheory
open SurfaceOfSpecZ _root_.RHTower HTGeometry CanonicalSystemOfTheWindowTower
/-- Translation energy of a physical complex L² state against the damped Green kernel. -/
def greenJumpEnergy (r : ℝ) (f : SoninL2) : ℝ :=
  ∫ t in Ioi (0 : ℝ), archDamped r t * ccmActualHeadTranslationDefect t f

/-- The critical energy retains infinity, so its domain is not assumed in advance. -/
def criticalGreenEnergy (f : SoninL2) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
    (archLevyDensity t * ccmActualHeadTranslationDefect t f)

private theorem continuous_defect (f : SoninL2) :
    Continuous fun t => ccmActualHeadTranslationDefect t f :=
  ((continuous_logTranslationCLM f).sub continuous_const).norm.pow 2

private theorem defect_nonneg (t : ℝ) (f : SoninL2) :
    0 ≤ ccmActualHeadTranslationDefect t f := sq_nonneg _

private theorem measurable_damped_defect (r : ℝ) (f : SoninL2) :
    Measurable fun t => archDamped r t * ccmActualHeadTranslationDefect t f := by
  exact (by unfold archDamped; fun_prop : Measurable (archDamped r)).mul
    (continuous_defect f).measurable

theorem integrable_greenJumpEnergy {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (f : SoninL2) : IntegrableOn
      (fun t => archDamped r t * ccmActualHeadTranslationDefect t f) (Ioi 0) := by
  refine ((integrable_archDamped hr0 hr1).mul_const (4 * ‖f‖ ^ 2)).integrableOn.mono'
    (measurable_damped_defect r f).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (mul_nonneg (archDamped_nonneg hr0 hr1 t) (defect_nonneg t f))]
  exact mul_le_mul_of_nonneg_left (ccmActualHeadTranslationDefect_le t f)
    (archDamped_nonneg hr0 hr1 t)

theorem greenJumpEnergy_nonneg (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (f : SoninL2) :
    0 ≤ greenJumpEnergy r f :=
  integral_nonneg fun t => mul_nonneg (archDamped_nonneg hr0 hr1 t) (sq_nonneg _)

theorem greenJumpEnergy_mono {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s < 1)
    (f : SoninL2) : greenJumpEnergy r f ≤ greenJumpEnergy s f := by
  apply integral_mono (integrable_greenJumpEnergy hr0 (hrs.trans_lt hs1) f)
    (integrable_greenJumpEnergy (hr0.trans hrs) hs1 f)
  intro t
  exact mul_le_mul_of_nonneg_right (archDamped_mono hr0 hrs hs1 t) (sq_nonneg _)

private theorem ofReal_greenJumpEnergy {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (f : SoninL2) : ENNReal.ofReal (greenJumpEnergy r f) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
        (archDamped r t * ccmActualHeadTranslationDefect t f) :=
  ofReal_integral_eq_lintegral_ofReal (integrable_greenJumpEnergy hr0 hr1 f)
    (Eventually.of_forall fun t => mul_nonneg (archDamped_nonneg hr0 hr1 t) (sq_nonneg _))

/-- The actual Green energies converge in the extended half-line for every L² state. -/
theorem tendsto_greenJumpEnergy_extended (f : SoninL2) :
    Tendsto (fun r => ENNReal.ofReal (greenJumpEnergy r f))
      (𝓝[<] (1 : ℝ)) (𝓝 (criticalGreenEnergy f)) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun r t =>
    ENNReal.ofReal (archDamped r t * ccmActualHeadTranslationDefect t f)
  have h0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlimit : ∀ t ∈ Ioi (0 : ℝ), Tendsto (fun r => F r t)
      (𝓝[<] (1 : ℝ)) (𝓝 (ENNReal.ofReal
        (archLevyDensity t * ccmActualHeadTranslationDefect t f))) := by
    intro t ht
    have h : Tendsto (fun r => ENNReal.ofReal (archDamped r t *
        ccmActualHeadTranslationDefect t f)) (𝓝[<] (1 : ℝ))
        (𝓝 (ENNReal.ofReal (archProfile |t| * ccmActualHeadTranslationDefect t f))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((tendsto_archDamped (ne_of_gt ht)).mono_left nhdsWithin_le_nhds).mul_const
        (ccmActualHeadTranslationDefect t f))
    simpa only [F, abs_of_pos (mem_Ioi.mp ht), SurfaceOfSpecZ.archProfile,
      _root_.RHTower.archLevyDensity] using h
  have hfatou := lintegral_liminf_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (u := 𝓝[<] (1 : ℝ)) (fun r => (measurable_damped_defect r f).ennreal_ofReal)
  have hleft : criticalGreenEnergy f ≤
      liminf (fun r => ∫⁻ t in Ioi (0 : ℝ), F r t) (𝓝[<] (1 : ℝ)) := by
    rw [show (∫⁻ t in Ioi (0 : ℝ), liminf (fun r => F r t) (𝓝[<] (1 : ℝ))) =
      criticalGreenEnergy f by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact (hlimit t ht).liminf_eq] at hfatou
    exact hfatou
  have hright : limsup (fun r => ∫⁻ t in Ioi (0 : ℝ), F r t)
      (𝓝[<] (1 : ℝ)) ≤ criticalGreenEnergy f := by
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right
      (archDamped_le_archProfile hr0.le (mem_Iio.mp hr1).le (ne_of_gt ht))
      (sq_nonneg ‖logTranslationCLM t f - f‖)
    simpa only [abs_of_pos (mem_Ioi.mp ht), SurfaceOfSpecZ.archProfile,
      _root_.RHTower.archLevyDensity, ccmActualHeadTranslationDefect] using h
  refine (tendsto_of_le_liminf_of_limsup_le hleft hright).congr' ?_
  filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
  exact (ofReal_greenJumpEnergy hr0.le (mem_Iio.mp hr1) f).symm

private theorem defect_eq_integral (f : SoninL2) (t : ℝ) :
    ccmActualHeadTranslationDefect t f = ∫ u : ℝ, ‖f u - f (u + t)‖ ^ 2 := by
  rw [ccmActualHeadTranslationDefect, _root_.RHTower.norm_sq_lp_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (logTranslationCLM t f) f, logTranslationCLM_ae t f]
    with u hsub hshift
  rw [hsub, Pi.sub_apply, hshift, norm_sub_rev]

/-- The critical Green energy has the exact Gamma Fourier multiplier. -/
theorem criticalGreenEnergy_eq_fourier (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : criticalGreenEnergy f.1 =
      ∫⁻ ξ : ℝ, ENNReal.ofReal
        (2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) *
          ‖fourierUnitary f.1 ξ‖ ^ 2) := by
  have hi := integrable_suzukiApertureHilbert a f
  rw [criticalGreenEnergy]
  simp_rw [defect_eq_integral]
  rw [← lintegral_archSymbol_mul_normSq_fourier hi (Lp.memLp f.1)]
  apply lintegral_congr_ae
  filter_upwards [fourierUnitary_ae_eq_fourier_of_integrable f.1 hi] with ξ hξ
  rw [hξ]

private theorem weight_eq_gamma (ξ : ℝ) : ccmArchimedeanFormWeight ξ =
    1 + 2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) := by
  unfold ccmArchimedeanFormWeight
  rcases le_total 0 ξ with hξ | hξ
  · rw [abs_of_nonneg hξ]
  · rw [abs_of_nonpos hξ, mul_neg, gammaHardyPhaseRate_neg]

/-- The complete Fourier graph norm is mass plus critical Green energy, even at infinity. -/
theorem weighted_energy_eq_mass_add_green (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (ccmArchimedeanFormWeight ξ *
      ‖fourierUnitary f.1 ξ‖ ^ 2)) = ENNReal.ofReal (‖f‖ ^ 2) + criticalGreenEnergy f.1 := by
  rw [criticalGreenEnergy_eq_fourier]
  have hpoint (ξ : ℝ) : ENNReal.ofReal (ccmArchimedeanFormWeight ξ *
      ‖fourierUnitary f.1 ξ‖ ^ 2) = ENNReal.ofReal (‖fourierUnitary f.1 ξ‖ ^ 2) +
      ENNReal.ofReal (2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) *
        ‖fourierUnitary f.1 ξ‖ ^ 2) := by
    rw [weight_eq_gamma, add_mul, one_mul, ENNReal.ofReal_add (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr
        (gammaHardyPhaseRate_zero_le_levy _))) (sq_nonneg _))]
  simp_rw [hpoint]
  rw [lintegral_add_left ((Lp.stronglyMeasurable (fourierUnitary f.1)).measurable.norm.pow_const 2 |>.ennreal_ofReal) _]
  have hsq := (Lp.memLp (fourierUnitary f.1)).integrable_norm_pow (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun ξ => sq_nonneg _),
    ← _root_.RHTower.norm_sq_lp_eq_integral_norm_sq, fourierUnitary.norm_map]
  rfl

/-- Finite critical Green energy characterizes the full logarithmic form domain. -/
theorem criticalGreenEnergy_ne_top_iff (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    criticalGreenEnergy f.1 ≠ ⊤ ↔ HasLogarithmicEnergy f.1 := by
  rw [hasLogarithmicEnergy_iff_ccm_weight]
  have hm : AEStronglyMeasurable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ *
      ‖fourierUnitary f.1 ξ‖ ^ 2) volume :=
    measurable_ccmArchimedeanFormWeight.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (fourierUnitary f.1)).norm.pow 2)
  rw [← lintegral_ofReal_ne_top_iff_integrable hm
    (Eventually.of_forall fun ξ => mul_nonneg (ccmArchimedeanFormWeight_pos ξ).le (sq_nonneg _)),
    weighted_energy_eq_mass_add_green]
  rw [ENNReal.add_ne_top]
  exact ⟨fun h => ⟨ENNReal.ofReal_ne_top, h⟩, fun h => h.2⟩

/-- No smoothness is needed: bounded Green energy is exactly admission to the actual Weil form. -/
theorem criticalGreenEnergy_ne_top_iff_form_range (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : criticalGreenEnergy f.1 ≠ ⊤ ↔
      ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f := by
  rw [criticalGreenEnergy_ne_top_iff]
  constructor
  · exact exists_ccm_form_of_logarithmicEnergy a f
  · rintro ⟨u, rfl⟩
    exact hasLogarithmicEnergy_ccm_form a u

/-- Outside the complete form domain the damped Green energies tend to positive infinity. -/
theorem tendsto_greenJumpEnergy_atTop (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (hf : ¬ HasLogarithmicEnergy f.1) :
    Tendsto (fun r => greenJumpEnergy r f.1) (𝓝[<] (1 : ℝ)) atTop := by
  have he : criticalGreenEnergy f.1 = ⊤ := by
    by_contra h
    exact hf ((criticalGreenEnergy_ne_top_iff a f).mp h)
  exact ENNReal.tendsto_ofReal_nhds_top.mp (he ▸ tendsto_greenJumpEnergy_extended f.1)

/-- On the domain the Green limit is an ordinary finite real limit. -/
theorem tendsto_greenJumpEnergy_finite (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (hf : HasLogarithmicEnergy f.1) :
    Tendsto (fun r => greenJumpEnergy r f.1) (𝓝[<] (1 : ℝ))
      (𝓝 (criticalGreenEnergy f.1).toReal) := by
  have h := (ENNReal.tendsto_toReal ((criticalGreenEnergy_ne_top_iff a f).mpr hf)).comp
    (tendsto_greenJumpEnergy_extended f.1)
  refine h.congr' ?_
  have h0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
  exact ENNReal.toReal_ofReal (greenJumpEnergy_nonneg r hr0.le (mem_Iio.mp hr1) f.1)

/-- Existence of any finite Green limit characterizes the complete Weil form domain. -/
theorem finite_green_limit_iff_form_range (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    (∃ L : ℝ, Tendsto (fun r => greenJumpEnergy r f.1) (𝓝[<] (1 : ℝ)) (𝓝 L)) ↔
      ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f := by
  rw [← criticalGreenEnergy_ne_top_iff_form_range]
  constructor
  · rintro ⟨L, hL⟩
    have he := tendsto_nhds_unique (tendsto_greenJumpEnergy_extended f.1)
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL)
    rw [he]
    exact ENNReal.ofReal_ne_top
  · intro hf
    exact ⟨_, tendsto_greenJumpEnergy_finite a f ((criticalGreenEnergy_ne_top_iff a f).mp hf)⟩

/-- The Green jump plus mass is exactly the complete form norm. -/
theorem criticalGreenEnergy_form_norm (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (criticalGreenEnergy (ccmArchimedeanFormToAperture a u).1).toReal +
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 = ‖u‖ ^ 2 := by
  let f := ccmArchimedeanFormToAperture a u
  have hf : HasLogarithmicEnergy f.1 := hasLogarithmicEnergy_ccm_form a u
  have hi := (hasLogarithmicEnergy_iff_ccm_weight f.1).mp hf
  have h := weighted_energy_eq_mass_add_green a f
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ξ =>
    mul_nonneg (ccmArchimedeanFormWeight_pos ξ).le (sq_nonneg _))] at h
  have hn : (∫ ξ : ℝ, ccmArchimedeanFormWeight ξ * ‖fourierUnitary f.1 ξ‖ ^ 2) =
      ‖u‖ ^ 2 := by
    change (∫ ξ : ℝ, ccmArchimedeanFormWeight ξ *
      ‖fourierUnitary (ccmArchimedeanFourierToTime u.1) ξ‖ ^ 2) = ‖u.1‖ ^ 2
    rw [fourierUnitary_ccmArchimedeanFourierToTime, norm_sq_ccmArchimedeanFourierL2]
    apply integral_congr_ae
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn u.1] with ξ hξ
    rw [hξ]
  rw [hn] at h
  have ht := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ((criticalGreenEnergy_ne_top_iff a f).mpr hf),
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _)] at ht
  linarith only [ht]

/-- The saturated arithmetic Green energy on every complex aperture L² state. -/
def greenWeilEnergy (a : SuzukiPositiveAperture) (r : ℝ)
    (f : suzukiApertureHilbert a) : ℝ :=
  greenJumpEnergy r f.1 + 2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
    (inner ℂ (ccmPolarOperator a f) f).re -
    (inner ℂ (ccmFinitePrimeOperator a f) f).re

private theorem greenWeilEnergy_eq_remainder (a : SuzukiPositiveAperture) (r : ℝ)
    (f : suzukiApertureHilbert a) : greenWeilEnergy a r f =
      greenJumpEnergy r f.1 + ‖f‖ ^ 2 +
        (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re := by
  have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
    norm_cast
  rw [greenWeilEnergy, inner_ccmRestrictedWeilBoundedRemainder,
    Complex.sub_re, Complex.add_re, Complex.mul_re, hself]
  unfold ccmArchimedeanRemainderScalar
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The actual damped Green construction reaches the literal closed Weil form on its whole domain. -/
theorem tendsto_greenWeilEnergy_form (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    Tendsto (fun r => greenWeilEnergy a r (ccmArchimedeanFormToAperture a u))
      (𝓝[<] (1 : ℝ)) (𝓝 (ccmRestrictedWeilForm a u u).re) := by
  have h := ((tendsto_greenJumpEnergy_finite a (ccmArchimedeanFormToAperture a u)
    (hasLogarithmicEnergy_ccm_form a u)).add_const
      (‖ccmArchimedeanFormToAperture a u‖ ^ 2)).add_const
      (inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re
  rw [criticalGreenEnergy_form_norm] at h
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u]
    norm_cast
  simpa only [greenWeilEnergy_eq_remainder, ccmRestrictedWeilForm, Complex.add_re,
    hself] using h

/-- Every precritical Green form is continuous on physical L², including nonsmooth states. -/
theorem continuous_greenJumpEnergy {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (greenJumpEnergy r) := by
  rw [continuous_iff_continuousAt]
  intro f₀
  apply continuousAt_of_dominated (bound := fun t => archDamped r t * (4 * (‖f₀‖ + 1) ^ 2))
  · filter_upwards with f
    exact (measurable_damped_defect r f).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds f₀ one_pos] with f hf
    have hfnorm : ‖f‖ ≤ ‖f₀‖ + 1 := by
      have hd : ‖f - f₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hf
      have ht : ‖f‖ ≤ ‖f - f₀‖ + ‖f₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (f - f₀) f₀
      linarith only [hd, ht]
    filter_upwards with t
    rw [Real.norm_of_nonneg (mul_nonneg (archDamped_nonneg hr0 hr1 t) (defect_nonneg t f))]
    apply mul_le_mul_of_nonneg_left _ (archDamped_nonneg hr0 hr1 t)
    exact (ccmActualHeadTranslationDefect_le t f).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg f) hfnorm 2) (by norm_num))
  · exact ((integrable_archDamped hr0 hr1).mul_const _).integrableOn
  · filter_upwards with t
    exact (continuous_const.mul
      (((logTranslationCLM t).continuous.sub continuous_id).norm.pow 2)).continuousAt

/-- A finite bound at every strict damping; no differentiability or Fourier moment is required. -/
theorem greenJumpEnergy_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (f : SoninL2) :
    greenJumpEnergy r f ≤ (∫ t in Ioi (0 : ℝ), archDamped r t) * (4 * ‖f‖ ^ 2) := by
  rw [← integral_mul_const]
  exact integral_mono (integrable_greenJumpEnergy hr0 hr1 f)
    (((integrable_archDamped hr0 hr1).mul_const _).integrableOn)
    (fun t => mul_le_mul_of_nonneg_left (ccmActualHeadTranslationDefect_le t f)
      (archDamped_nonneg hr0 hr1 t))

/-- The saturated prime and polar terms cannot cancel an infinite critical Green energy. -/
theorem tendsto_greenWeilEnergy_atTop (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (hf : ¬ HasLogarithmicEnergy f.1) :
    Tendsto (fun r => greenWeilEnergy a r f) (𝓝[<] (1 : ℝ)) atTop := by
  have h := tendsto_atTop_add_const_right _ (‖f‖ ^ 2)
    (tendsto_greenJumpEnergy_atTop a f hf)
  simpa only [greenWeilEnergy_eq_remainder] using
    tendsto_atTop_add_const_right _
      (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re h

/-- Finite convergence of the full saturated Green form detects exactly its closed Weil domain. -/
theorem finite_greenWeil_limit_iff_form_range (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    (∃ L : ℝ, Tendsto (fun r => greenWeilEnergy a r f) (𝓝[<] (1 : ℝ)) (𝓝 L)) ↔
      ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f := by
  constructor
  · rintro ⟨L, hL⟩
    apply (finite_green_limit_iff_form_range a f).mp
    refine ⟨L - (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re - ‖f‖ ^ 2, ?_⟩
    have h := (hL.sub_const (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re).sub_const
      (‖f‖ ^ 2)
    simpa only [greenWeilEnergy_eq_remainder, add_sub_cancel_right] using h
  · rintro ⟨u, rfl⟩
    exact ⟨_, tendsto_greenWeilEnergy_form a u⟩

end GaloisForLFunctions.HyperbolicArakelovTheory

#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.tendsto_greenJumpEnergy_extended
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.finite_green_limit_iff_form_range
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.continuous_greenJumpEnergy
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.criticalGreenEnergy_form_norm
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.tendsto_greenWeilEnergy_form
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.finite_greenWeil_limit_iff_form_range
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.tendsto_greenWeilEnergy_atTop
