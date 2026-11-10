import GaloisForLFunctions.HyperbolicArakelovTheory.TheFiniteScatteringTowerHasAnExactArithmeticJumpKernel
import GaloisForLFunctions.HyperbolicArakelovTheory.TheGreenDampingDetectsTheCompleteWeilFormDomain
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedPolarFactorization
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadQuantileGammaChiSquareProducer

/-!
# The geometric scattering tower detects the complete Weil form domain

The exact finite-height packet formula extends the raw primitive-pair
scattering energies continuously to each aperture L² space. Its positive
jump kernels increase to the critical Green density, while the mass and
finite-prime corrections converge. Consequently its finite limiting
domain is exactly the complete Weil form domain. On that domain the limit
is the literal closed Weil form; outside it the energies tend to positive
infinity.

The smooth-source identity fixes this extension from the raw geometric
construction, including both polar moments and every prime contact.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter Set Topology
open scoped Classical ENNReal BigOperators InnerProductSpace
namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
open _root_.RHTower Zeta23 Zeta23.WeilEF

/-- The finite scattering height acts on every physical L² state. -/
def scatteringJumpEnergy (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ t in Ioi (0 : ℝ), scatteringCutoffKernel N t * ccmActualHeadTranslationDefect t f

private theorem integrable_scatteringCutoffKernel (N : ℕ) :
    IntegrableOn (scatteringCutoffKernel N) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => (N : ℝ) * Real.exp (-t / 2)) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (N : ℝ)).congr (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [show -(1 / 2 : ℝ) * t = -t / 2 by ring]
  refine hb.mono' (continuous_scatteringCutoffKernel N).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (scatteringCutoffKernel_nonneg N t)]
  exact scatteringCutoffKernel_bound N ht.le

private theorem continuous_scatteringDefect (f : SoninL2) :
    Continuous fun t => ccmActualHeadTranslationDefect t f :=
  ((continuous_logTranslationCLM f).sub continuous_const).norm.pow 2

theorem integrable_scatteringJumpEnergy (N : ℕ) (f : SoninL2) :
    IntegrableOn (fun t => scatteringCutoffKernel N t * ccmActualHeadTranslationDefect t f)
      (Ioi (0 : ℝ)) := by
  refine ((integrable_scatteringCutoffKernel N).mul_const (4 * ‖f‖ ^ 2)).mono'
    ((continuous_scatteringCutoffKernel N).mul (continuous_scatteringDefect f)).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (mul_nonneg (scatteringCutoffKernel_nonneg N t)
    (show 0 ≤ ccmActualHeadTranslationDefect t f from sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left (ccmActualHeadTranslationDefect_le t f)
    (scatteringCutoffKernel_nonneg N t)

theorem scatteringJumpEnergy_nonneg (N : ℕ) (f : SoninL2) :
    0 ≤ scatteringJumpEnergy N f :=
  integral_nonneg fun t => mul_nonneg (scatteringCutoffKernel_nonneg N t) (sq_nonneg _)

private theorem scatteringCutoffKernel_mono (t : ℝ) : Monotone (fun N => scatteringCutoffKernel N t) := by
  intro N M hNM
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.exp_pos _).le (by positivity))
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
    (fun j _ _ => (Real.exp_pos _).le)

private theorem tendsto_scatteringCutoffKernel {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => scatteringCutoffKernel N t) atTop (𝓝 (archLevyDensity t)) := by
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have he (N : ℕ) : Real.exp (-(N : ℝ) * t) = Real.exp (-t) ^ N := by
    rw [show -(N : ℝ) * t = (N : ℝ) * (-t) by ring, Real.exp_nat_mul]
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).mul_const (archLevyDensity t)
  simp only [sub_zero, one_mul] at h
  exact h.congr fun N => by rw [scatteringCutoffKernel_eq N ht, he]

/-- The finite-height jump energies increase to the critical Green energy, including infinity. -/
theorem tendsto_scatteringJumpEnergy_extended (f : SoninL2) :
    Tendsto (fun N => ENNReal.ofReal (scatteringJumpEnergy N f)) atTop
      (𝓝 (criticalGreenEnergy f)) := by
  have h := lintegral_tendsto_of_tendsto_of_monotone
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun N t => ENNReal.ofReal (scatteringCutoffKernel N t * ccmActualHeadTranslationDefect t f))
    (F := fun t => ENNReal.ofReal (archLevyDensity t * ccmActualHeadTranslationDefect t f))
    (fun N => (((continuous_scatteringCutoffKernel N).mul
      (continuous_scatteringDefect f)).measurable.ennreal_ofReal).aemeasurable)
    (Eventually.of_forall fun t N M hNM => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (scatteringCutoffKernel_mono t hNM) (sq_nonneg _)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_scatteringCutoffKernel ht).mul_const (ccmActualHeadTranslationDefect t f)))
  have he (N : ℕ) : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
      (scatteringCutoffKernel N t * ccmActualHeadTranslationDefect t f)) =
      ENNReal.ofReal (scatteringJumpEnergy N f) := by
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_scatteringJumpEnergy N f)
      (Eventually.of_forall fun t => mul_nonneg (scatteringCutoffKernel_nonneg N t) (sq_nonneg _))).symm
  simpa only [he, criticalGreenEnergy] using h

/-- Finite scattering-jump convergence is precisely the complete Weil form domain. -/
theorem finite_scatteringJump_limit_iff_form_range (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    (∃ L : ℝ, Tendsto (fun N => scatteringJumpEnergy N f.1) atTop (𝓝 L)) ↔
      ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f := by
  rw [← criticalGreenEnergy_ne_top_iff_form_range]
  constructor
  · rintro ⟨L, hL⟩
    have h := tendsto_nhds_unique (tendsto_scatteringJumpEnergy_extended f.1)
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL)
    rw [h]
    exact ENNReal.ofReal_ne_top
  · intro hf
    refine ⟨(criticalGreenEnergy f.1).toReal, ?_⟩
    have h := (ENNReal.tendsto_toReal hf).comp (tendsto_scatteringJumpEnergy_extended f.1)
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (scatteringJumpEnergy_nonneg _ _)] using h

/-- Every finite-height jump form is continuous in physical L². -/
theorem continuous_scatteringJumpEnergy (N : ℕ) : Continuous (scatteringJumpEnergy N) := by
  rw [continuous_iff_continuousAt]
  intro f₀
  apply continuousAt_of_dominated (bound := fun t => scatteringCutoffKernel N t * (4 * (‖f₀‖ + 1) ^ 2))
  · filter_upwards with f
    exact ((continuous_scatteringCutoffKernel N).mul (continuous_scatteringDefect f)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds f₀ one_pos] with f hf
    have hfnorm : ‖f‖ ≤ ‖f₀‖ + 1 := by
      have hd : ‖f - f₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hf
      have ht : ‖f‖ ≤ ‖f - f₀‖ + ‖f₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (f - f₀) f₀
      linarith only [hd, ht]
    filter_upwards with t
    rw [Real.norm_of_nonneg (mul_nonneg (scatteringCutoffKernel_nonneg N t)
    (show 0 ≤ ccmActualHeadTranslationDefect t f from sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left ((ccmActualHeadTranslationDefect_le t f).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg f) hfnorm 2) (by norm_num)))
        (scatteringCutoffKernel_nonneg N t)
  · exact (integrable_scatteringCutoffKernel N).mul_const _
  · filter_upwards with t
    exact (continuous_const.mul
      (((logTranslationCLM t).continuous.sub continuous_id).norm.pow 2)).continuousAt

/-- The mass term fixed by the finite geometric Robin subtraction. -/
def scatteringMassCoefficient (N : ℕ) : ℝ :=
  2 * (robinCounterterm ((3 / 2 : ℝ) + N)).re -
    2 * ∫ t in Ioi (0 : ℝ), scatteringCutoffKernel N t

private theorem gamma_center_re :
    (logDeriv Complex.Gammaℝ (1 / 2 : ℂ)).re = gammaHardyPhaseRate 0 := by
  rw [logDeriv_Gammaℝ (by norm_num)]
  unfold gammaRealLogConnection gammaHardyPhaseRate linePt
  norm_num
  ring

private theorem integral_scatteringCutoffKernel (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), scatteringCutoffKernel N t) =
      (logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + N)).re - gammaHardyPhaseRate 0 := by
  have h := laplace_scatteringCutoffKernel N (s := (1 / 2 : ℂ)) (by norm_num)
  simp only [sub_self, neg_zero, zero_mul, Complex.exp_zero, mul_one] at h
  have hcast : (∫ t in Ioi (0 : ℝ), (scatteringCutoffKernel N t : ℂ)) =
      Complex.ofReal (∫ t in Ioi (0 : ℝ), scatteringCutoffKernel N t) := integral_ofReal
  rw [hcast] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.sub_re, gamma_center_re] using hr

private theorem robin_unit_increment (N : ℕ) :
    (robinCounterterm ((3 / 2 : ℝ) + N) - robinCounterterm ((1 / 2 : ℝ) + N)).re =
      Real.log (1 + 1 / ((1 / 2 : ℝ) + N)) / 2 := by
  have hN : (0 : ℝ) < 1 / 2 + N := by positivity
  have hM : (0 : ℝ) < 3 / 2 + N := by positivity
  rw [robinCounterterm_eq hM, robinCounterterm_eq hN, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_re]
  have hl : Real.log ((3 / 2 + (N : ℝ)) / 2) - Real.log ((1 / 2 + (N : ℝ)) / 2) =
      Real.log (1 + 1 / ((1 / 2 : ℝ) + N)) := by
    rw [← Real.log_div (by positivity : (3 / 2 + (N : ℝ)) / 2 ≠ 0)
      (by positivity : (1 / 2 + (N : ℝ)) / 2 ≠ 0)]
    congr 1
    field_simp
    ring
  linear_combination hl / 2

/-- The finite geometric scalar converges to the literal archimedean mass constant. -/
theorem tendsto_scatteringMassCoefficient :
    Tendsto scatteringMassCoefficient atTop (𝓝 (2 * gammaHardyPhaseRate 0)) := by
  have hr : Tendsto (fun N : ℕ => (1 / 2 : ℝ) + N) atTop atTop :=
    Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hgamma : Tendsto (fun N : ℕ =>
      logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + N) - robinCounterterm ((1 / 2 : ℝ) + N))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hr.const_div_atTop 3)
    filter_upwards [hr.eventually_ge_atTop 4] with N hN
    simpa using norm_gamma_sub_robinCounterterm
      (s := (1 / 2 : ℂ) + N) (by simpa using hN)
  have hratio : Tendsto (fun N : ℕ => 1 + 1 / ((1 / 2 : ℝ) + N)) atTop (𝓝 1) := by
    simpa only [add_zero] using (hr.const_div_atTop 1).const_add 1
  have hlog : Tendsto (fun N : ℕ => Real.log (1 + 1 / ((1 / 2 : ℝ) + N)) / 2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one, zero_div] using
      ((Real.continuousAt_log one_ne_zero).tendsto.comp hratio).div_const 2
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hgamma
  simp only [Function.comp_def, Complex.zero_re] at hreal
  have h := (((tendsto_const_nhds (x := 2 * gammaHardyPhaseRate 0)).sub
    (hreal.const_mul 2)).add (hlog.const_mul 2))
  simp only [mul_zero, sub_zero, add_zero] at h
  refine h.congr fun N => ?_
  rw [scatteringMassCoefficient, integral_scatteringCutoffKernel,
    ← robin_unit_increment, Complex.sub_re, Complex.sub_re]
  ring

/-- Prime contacts retained by the actual finite scattering height on a physical aperture. -/
def scatteringPrimeOperator (a : SuzukiPositiveAperture) (N : ℕ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
    (scatteringHeightMangoldt N n : ℂ) • ccmPrimeTransportOperator a n

private theorem tendsto_scatteringHeightMangoldt {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun N => (scatteringHeightMangoldt N n : ℂ)) atTop
      (𝓝 (ArithmeticFunction.vonMangoldt n : ℂ)) := by
  have hnR : (1 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hi0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hi1 : (n : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hnR
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).const_mul
    (ArithmeticFunction.vonMangoldt n : ℝ))
  simp only [sub_zero, mul_one] at h
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp h

/-- On a fixed aperture the finite scattering prime operators converge in operator norm. -/
theorem tendsto_scatteringPrimeOperator (a : SuzukiPositiveAperture) :
    Tendsto (scatteringPrimeOperator a) atTop (𝓝 (ccmFinitePrimeOperator a)) := by
  letI : NormedAddCommGroup (suzukiApertureHilbert a) := inferInstance
  letI : NormedSpace ℂ (suzukiApertureHilbert a) := inferInstance
  letI : NormedAddCommGroup (suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a) := inferInstance
  unfold scatteringPrimeOperator ccmFinitePrimeOperator
  apply tendsto_finsetSum
  intro n hn
  exact (tendsto_scatteringHeightMangoldt (Finset.mem_Icc.mp hn).1).smul_const _

/-- The continuous finite-height form with the normalization fixed by the raw geometric tower. -/
def scatteringWeilEnergy (a : SuzukiPositiveAperture) (N : ℕ)
    (f : suzukiApertureHilbert a) : ℝ :=
  scatteringJumpEnergy N f.1 + scatteringMassCoefficient N * ‖f‖ ^ 2 +
    (inner ℂ (ccmPolarOperator a f) f).re -
    (inner ℂ (scatteringPrimeOperator a N f) f).re

/-- Every finite geometric scattering height extends continuously to aperture L². -/
theorem continuous_scatteringWeilEnergy (a : SuzukiPositiveAperture) (N : ℕ) :
    Continuous (scatteringWeilEnergy a N) := by
  unfold scatteringWeilEnergy
  refine (((continuous_scatteringJumpEnergy N).comp continuous_subtype_val).add
    (continuous_const.mul (continuous_norm.pow 2))).add ?_ |>.sub ?_
  · exact Complex.continuous_re.comp ((ccmPolarOperator a).continuous.inner continuous_id)
  · exact Complex.continuous_re.comp ((scatteringPrimeOperator a N).continuous.inner continuous_id)

private theorem tendsto_scattering_remainder (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    Tendsto (fun N => scatteringMassCoefficient N * ‖f‖ ^ 2 +
      (inner ℂ (ccmPolarOperator a f) f).re - (inner ℂ (scatteringPrimeOperator a N f) f).re)
      atTop (𝓝 (2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        (inner ℂ (ccmPolarOperator a f) f).re - (inner ℂ (ccmFinitePrimeOperator a f) f).re)) := by
  have heval : Continuous (fun T : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a => T f) := by
    fun_prop
  have hp := heval.continuousAt.tendsto.comp (tendsto_scatteringPrimeOperator a)
  have hi := hp.inner (𝕜 := ℂ) (tendsto_const_nhds (x := f))
  exact ((tendsto_scatteringMassCoefficient.mul_const _).add_const _).sub
    (Complex.continuous_re.continuousAt.tendsto.comp hi)

/-- The finite scattering form converges to the literal Weil form throughout its complete domain. -/
theorem tendsto_scatteringWeilEnergy_form (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    Tendsto (fun N => scatteringWeilEnergy a N (ccmArchimedeanFormToAperture a u)) atTop
      (𝓝 (ccmRestrictedWeilForm a u u).re) := by
  let f := ccmArchimedeanFormToAperture a u
  have hf : criticalGreenEnergy f.1 ≠ ⊤ :=
    (criticalGreenEnergy_ne_top_iff_form_range a f).mpr ⟨u, rfl⟩
  have hj := (ENNReal.tendsto_toReal hf).comp (tendsto_scatteringJumpEnergy_extended f.1)
  simp only [Function.comp_def, ENNReal.toReal_ofReal (scatteringJumpEnergy_nonneg _ _)] at hj
  have h := hj.add (tendsto_scattering_remainder a f)
  have hrem : 2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
      (inner ℂ (ccmPolarOperator a f) f).re - (inner ℂ (ccmFinitePrimeOperator a f) f).re =
      ‖f‖ ^ 2 + (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re := by
    have hs : (inner ℂ f f).re = ‖f‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
      norm_cast
    rw [inner_ccmRestrictedWeilBoundedRemainder, Complex.sub_re, Complex.add_re,
      Complex.mul_re, hs]
    unfold ccmArchimedeanRemainderScalar
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hrem, ← add_assoc, criticalGreenEnergy_form_norm] at h
  have hs : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u]
    norm_cast
  simpa only [scatteringWeilEnergy, ccmRestrictedWeilForm, Complex.add_re, hs,
    add_assoc, add_sub_assoc, f] using h

/-- Outside the exact form domain, the finite scattering energies diverge to positive infinity. -/
theorem tendsto_scatteringWeilEnergy_atTop (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a)
    (hf : ¬ ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f) :
    Tendsto (fun N => scatteringWeilEnergy a N f) atTop atTop := by
  have hc : criticalGreenEnergy f.1 = ⊤ := by
    by_contra h
    exact hf ((criticalGreenEnergy_ne_top_iff_form_range a f).mp h)
  have hj : Tendsto (fun N => scatteringJumpEnergy N f.1) atTop atTop :=
    ENNReal.tendsto_ofReal_nhds_top.mp (hc ▸ tendsto_scatteringJumpEnergy_extended f.1)
  let R := 2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
    (inner ℂ (ccmPolarOperator a f) f).re - (inner ℂ (ccmFinitePrimeOperator a f) f).re
  have hR := (tendsto_scattering_remainder a f).eventually
    (Ioi_mem_nhds (show R - 1 < R by linarith only))
  apply tendsto_atTop.2
  intro b
  filter_upwards [hj.eventually_ge_atTop (b - R + 1), hR] with N hN hRN
  change R - 1 < _ at hRN
  unfold scatteringWeilEnergy
  linarith only [hN, hRN]

/-- A finite limit of the actual finite-height extension is equivalent to admission to the Weil form. -/
theorem finite_scatteringWeil_limit_iff_form_range (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    (∃ L : ℝ, Tendsto (fun N => scatteringWeilEnergy a N f) atTop (𝓝 L)) ↔
      ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f := by
  constructor
  · rintro ⟨L, hL⟩
    apply (finite_scatteringJump_limit_iff_form_range a f).mp
    have h := hL.sub (tendsto_scattering_remainder a f)
    refine ⟨_, h.congr fun N => ?_⟩
    unfold scatteringWeilEnergy
    ring
  · rintro ⟨u, rfl⟩
    exact ⟨_, tendsto_scatteringWeilEnergy_form a u⟩

private theorem correlation_eq_weilTest {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    (ccmComplexSmoothCrossCorrelation u v : ℝ → ℂ) = EF.weilTest v u := by
  funext t
  rw [ccmComplexSmoothCrossCorrelation_apply, EF.weilTest, convolution_def]
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, neg_sub, Complex.star_def]

private theorem correlation_zero_eq_mass {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ccmComplexSmoothCrossCorrelation u u 0 =
      (‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 : ℝ) := by
  have h := inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation u u 0
  rw [logTranslationCLM_zero_apply, neg_zero, inner_self_eq_norm_sq_to_K] at h
  have hn : ‖(ccmArchimedeanFormToAperture a u.toCCMFormVector).1‖ =
      ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ := rfl
  rw [hn] at h
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using h.symm

private theorem correlation_pair_re {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (t : ℝ) :
    (ccmComplexSmoothCrossCorrelation u u t + ccmComplexSmoothCrossCorrelation u u (-t)).re =
      2 * ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 -
        ccmActualHeadTranslationDefect t (ccmArchimedeanFormToAperture a u.toCCMFormVector).1 := by
  have h := logTranslation_defect_eq t (ccmArchimedeanFormToAperture a u.toCCMFormVector).1
  rw [inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation,
    inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation, neg_neg] at h
  change ccmActualHeadTranslationDefect t (ccmArchimedeanFormToAperture a u.toCCMFormVector).1 = _ at h
  rw [add_comm (ccmComplexSmoothCrossCorrelation u u (-t))] at h
  have hn : ‖(ccmArchimedeanFormToAperture a u.toCCMFormVector).1‖ =
      ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ := rfl
  rw [hn] at h
  linarith only [h]

private theorem Hfn_real_eq_exp_integral (k : ℝ → ℂ) (s : ℝ) :
    Hfn k (s : ℂ) = ∫ t : ℝ, (Real.exp ((s - 1 / 2) * t) : ℂ) * k t := by
  have h := Hfn_line k s 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  rw [h, paperFT]
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one, tilt]
  apply integral_congr_ae
  filter_upwards with t
  exact mul_comm _ _

private theorem correlation_polar_eq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Hfn (ccmComplexSmoothCrossCorrelation u u) 0 + Hfn (ccmComplexSmoothCrossCorrelation u u) 1 =
      inner ℂ (ccmPolarOperator a (ccmArchimedeanFormToAperture a u.toCCMFormVector))
        (ccmArchimedeanFormToAperture a u.toCCMFormVector) := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by rfl,
    show (1 : ℂ) = ((1 : ℝ) : ℂ) by rfl,
    Hfn_real_eq_exp_integral, Hfn_real_eq_exp_integral,
    integral_exp_mul_ccmComplexSmoothCrossCorrelation,
    integral_exp_mul_ccmComplexSmoothCrossCorrelation,
    inner_ccmPolarOperator]
  simp_rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector]
  norm_num
  ring

private theorem scatteringPrime_source {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (N : ℕ) :
    (∑' n : ℕ, (scatteringHeightMangoldt N n : ℂ) / Real.sqrt n *
      (ccmComplexSmoothCrossCorrelation u u (Real.log n) +
        ccmComplexSmoothCrossCorrelation u u (-Real.log n))) =
      inner ℂ (scatteringPrimeOperator a N (ccmArchimedeanFormToAperture a u.toCCMFormVector))
        (ccmArchimedeanFormToAperture a u.toCCMFormVector) := by
  rw [tsum_eq_sum (s := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))))]
  · unfold scatteringPrimeOperator
    rw [_root_.sum_apply, sum_inner]
    apply Finset.sum_congr rfl
    intro n hn
    rw [_root_.smul_apply, inner_smul_left, Complex.conj_ofReal,
      inner_ccmPrimeTransportOperator,
      inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation,
      inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation, neg_neg]
    push_cast
    ring
  · intro n hn
    by_cases hsmall : n < 2
    · interval_cases n <;> simp [scatteringHeightMangoldt]
    · have hn2 : 2 ≤ n := le_of_not_gt hsmall
      have hlarge : Nat.floor (Real.exp (2 * a.1)) < n := by
        simpa only [Finset.mem_Icc, hn2, true_and, not_le] using hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
      have hlog : 2 * a.1 < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr
        ((Nat.floor_lt (Real.exp_nonneg _)).mp hlarge)
      have habs : 2 * a.1 ≤ |Real.log n| := hlog.le.trans (le_abs_self _)
      rw [ccmComplexSmoothCrossCorrelation_eq_zero_of_two_aperture_le_abs u u habs,
        ccmComplexSmoothCrossCorrelation_eq_zero_of_two_aperture_le_abs u u (by simpa only [abs_neg] using habs),
        add_zero, mul_zero]

private theorem cutoff_correlation_re {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), (scatteringCutoffKernel N t : ℂ) *
      (ccmComplexSmoothCrossCorrelation u u t + ccmComplexSmoothCrossCorrelation u u (-t))).re =
      2 * ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 *
        (∫ t in Ioi (0 : ℝ), scatteringCutoffKernel N t) -
          scatteringJumpEnergy N (ccmArchimedeanFormToAperture a u.toCCMFormVector).1 := by
  let k : ℝ → ℂ := ccmComplexSmoothCrossCorrelation u u
  have hk : Continuous k := (ccmComplexSmoothCrossCorrelation u u).continuous
  have hkc : HasCompactSupport k := by
    rw [show k = EF.weilTest u u from correlation_eq_weilTest u u]
    exact EF.weilTest_hasCompactSupport u.hasCompactSupport u.hasCompactSupport
  have hi : IntegrableOn (fun t : ℝ => (scatteringCutoffKernel N t : ℂ) * (k t + k (-t))) (Ioi 0) :=
    (((Complex.continuous_ofReal.comp (continuous_scatteringCutoffKernel N)).mul
      (hk.add (hk.comp continuous_neg))).integrable_of_hasCompactSupport
        ((hkc.add (hkc.comp_homeomorph (Homeomorph.neg ℝ))).mul_left)).integrableOn
  have hre := (integral_re (𝕜 := ℂ) hi).symm
  simp only [RCLike.re_to_complex, k] at hre
  rw [hre]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, correlation_pair_re, mul_sub]
  rw [integral_sub ((integrable_scatteringCutoffKernel N).mul_const _)
    (integrable_scatteringJumpEnergy N _), integral_mul_const]
  change _ = _ - scatteringJumpEnergy N _
  rw [scatteringJumpEnergy]
  ring

/-- The continuous L² form is the extension of the actual raw geometric energies. -/
theorem rawEnergy_smooth_eq_scatteringWeilEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (N : ℕ) :
    (RawGeometry.energy u N).re =
      scatteringWeilEnergy a N (ccmArchimedeanFormToAperture a u.toCCMFormVector) := by
  rw [rawEnergy_eq_cutoff (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) u.hasCompactSupport,
    ← correlation_eq_weilTest u u, scatteringPhysicalPacket]
  rw [show 2 * robinCounterterm ((3 / 2 : ℝ) + N) * ccmComplexSmoothCrossCorrelation u u 0 +
      Hfn (ccmComplexSmoothCrossCorrelation u u) 0 + Hfn (ccmComplexSmoothCrossCorrelation u u) 1 =
    2 * robinCounterterm ((3 / 2 : ℝ) + N) * ccmComplexSmoothCrossCorrelation u u 0 +
      (Hfn (ccmComplexSmoothCrossCorrelation u u) 0 + Hfn (ccmComplexSmoothCrossCorrelation u u) 1) by ring,
    correlation_zero_eq_mass, correlation_polar_eq, scatteringPrime_source,
    Complex.sub_re, Complex.sub_re, Complex.add_re, cutoff_correlation_re]
  unfold scatteringWeilEnergy scatteringMassCoefficient
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  norm_num
  ring


/-- Every finite-height prime operator retains the Hermitian arithmetic pairing. -/
theorem scatteringPrimeOperator_isSelfAdjoint (a : SuzukiPositiveAperture) (N : ℕ) :
    IsSelfAdjoint (scatteringPrimeOperator a N) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold scatteringPrimeOperator
  generalize Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn, ContinuousLinearMap.adjoint.map_add, ih]
      have hnself := ccmPrimeTransportOperator_isSelfAdjoint a n
      rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hnself
      rw [ContinuousLinearMap.adjoint.map_smulₛₗ, hnself, Complex.conj_ofReal]

private theorem correlation_conj {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (t : ℝ) :
    (starRingEnd ℂ) (ccmComplexSmoothCrossCorrelation u u t) =
      ccmComplexSmoothCrossCorrelation u u (-t) := by
  let f := (ccmArchimedeanFormToAperture a u.toCCMFormVector).1
  have h := inner_conj_symm (𝕜 := ℂ) f (logTranslationCLM (-t) f)
  rw [← inner_logTranslationCLM t f f] at h
  dsimp only [f] at h
  rwa [inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation,
    inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation, neg_neg] at h

private theorem cutoff_correlation_im {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), (scatteringCutoffKernel N t : ℂ) *
      (ccmComplexSmoothCrossCorrelation u u t + ccmComplexSmoothCrossCorrelation u u (-t))).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_mul, map_add, Complex.conj_ofReal, correlation_conj, neg_neg]
  ring

/-- The finite raw geometric autocorrelation energy is real, before taking the tower limit. -/
theorem rawEnergy_smooth_im {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (N : ℕ) :
    (RawGeometry.energy u N).im = 0 := by
  let f := ccmArchimedeanFormToAperture a u.toCCMFormVector
  have hreal (T : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)
      (hT : IsSelfAdjoint T) : (inner ℂ (T f) f).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    exact (inner_conj_symm (𝕜 := ℂ) f (T f)).trans (hT.isSymmetric f f).symm
  rw [rawEnergy_eq_cutoff (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) u.hasCompactSupport,
    ← correlation_eq_weilTest u u, scatteringPhysicalPacket]
  rw [show 2 * robinCounterterm ((3 / 2 : ℝ) + N) * ccmComplexSmoothCrossCorrelation u u 0 +
      Hfn (ccmComplexSmoothCrossCorrelation u u) 0 + Hfn (ccmComplexSmoothCrossCorrelation u u) 1 =
    2 * robinCounterterm ((3 / 2 : ℝ) + N) * ccmComplexSmoothCrossCorrelation u u 0 +
      (Hfn (ccmComplexSmoothCrossCorrelation u u) 0 + Hfn (ccmComplexSmoothCrossCorrelation u u) 1) by ring,
    correlation_zero_eq_mass, correlation_polar_eq, scatteringPrime_source,
    Complex.sub_im, Complex.sub_im, Complex.add_im, cutoff_correlation_im,
    hreal _ (ccmPolarOperator_isSelfAdjoint a),
    hreal _ (scatteringPrimeOperator_isSelfAdjoint a N),
    robinCounterterm_eq (by positivity)]
  norm_num [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.mul_im]

/-- The full complex raw energy equals the continuous real L² form on its smooth core. -/
theorem rawEnergy_smooth_eq_ofReal_scatteringWeilEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (N : ℕ) :
    RawGeometry.energy u N =
      Complex.ofReal (scatteringWeilEnergy a N
        (ccmArchimedeanFormToAperture a u.toCCMFormVector)) := by
  apply Complex.ext
  · exact rawEnergy_smooth_eq_scatteringWeilEnergy u N
  · exact rawEnergy_smooth_im u N

#print axioms rawEnergy_smooth_eq_ofReal_scatteringWeilEnergy
#print axioms tendsto_scatteringWeilEnergy_form
#print axioms tendsto_scatteringWeilEnergy_atTop
#print axioms finite_scatteringWeil_limit_iff_form_range

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
