import GaloisForLFunctions.RHTower.CCMGeneralFourierWeightCompactEmbedding
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.RHTower.SuzukiHlogDenseFormCore
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Exact Hilbert form domain of the CCM archimedean Weil term

Connes--Consani's semilocal Weil form has archimedean spectral density

`2 * theta'(t)` with Plancherel measure `dt / (2*pi)`.

In the unitary Fourier convention used by this project, `t = 2*pi*xi`; hence the literal density
is `2 * gammaHardyPhaseRate (2*pi*xi)`.  Its global minimum is attained at zero.  Adding the exact
constant `1 - 2 * gammaHardyPhaseRate 0` produces a weight at least one.  This module constructs
the resulting weighted Fourier `L2` space, restricts its inverse Fourier transform to a bounded
aperture, and proves that its inclusion in physical `L2` is compact.

This is stronger than replacing theta-prime by an asymptotically equivalent logarithmic weight:
the original archimedean form is exactly the form-domain norm plus one scalar `L2` term.
-/

open MeasureTheory Set Filter
open scoped ENNReal InnerProduct Topology

noncomputable section

namespace RHTower

/-- Exact shifted CCM archimedean Fourier weight in the unitary Fourier variable. -/
def ccmArchimedeanFormWeight (xi : ℝ) : ℝ :=
  1 + 2 * (gammaHardyPhaseRate (2 * Real.pi * |xi|) - gammaHardyPhaseRate 0)

theorem one_le_ccmArchimedeanFormWeight (xi : ℝ) :
    1 ≤ ccmArchimedeanFormWeight xi := by
  have harg : gammaHardyPhaseRate 0 ≤
      gammaHardyPhaseRate (2 * Real.pi * |xi|) := by
    by_cases hxi : xi = 0
    · simp [hxi]
    · exact (gammaHardyPhaseRate_zero_lt
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (abs_ne_zero.mpr hxi))).le
  unfold ccmArchimedeanFormWeight
  linarith

theorem ccmArchimedeanFormWeight_pos (xi : ℝ) :
    0 < ccmArchimedeanFormWeight xi :=
  lt_of_lt_of_le zero_lt_one (one_le_ccmArchimedeanFormWeight xi)

theorem measurable_ccmArchimedeanFormWeight :
    Measurable ccmArchimedeanFormWeight := by
  unfold ccmArchimedeanFormWeight
  exact measurable_const.add (measurable_const.mul
    ((continuous_gammaHardyPhaseRate.measurable.comp
      (measurable_const.mul measurable_abs)).sub measurable_const))

/-- The source weight, bundled for the general CCM compact-embedding theorem. -/
def ccmArchimedeanFourierWeight : CCMFourierWeight where
  value u := 1 + 2 * (gammaHardyPhaseRate (2 * Real.pi * u) - gammaHardyPhaseRate 0)
  one_le_of_nonneg := by
    intro u hu
    have harg : gammaHardyPhaseRate 0 ≤ gammaHardyPhaseRate (2 * Real.pi * u) := by
      by_cases hu0 : u = 0
      · simp [hu0]
      · exact (gammaHardyPhaseRate_zero_lt
          (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hu0)).le
    linarith
  monotoneOn_nonneg := by
    intro x hx y hy hxy
    have hscale : 2 * Real.pi * x ≤ 2 * Real.pi * y :=
      mul_le_mul_of_nonneg_left hxy (mul_nonneg (by norm_num) Real.pi_pos.le)
    have hmono := strictMonoOn_gammaHardyPhaseRate.monotoneOn
      (Set.mem_Ici.mpr (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hx))
      (Set.mem_Ici.mpr (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hy)) hscale
    linarith
  tendsto_atTop := by
    have hscale : Tendsto (fun u : ℝ => 2 * Real.pi * u) atTop atTop :=
      tendsto_id.const_mul_atTop (mul_pos (by norm_num) Real.pi_pos)
    have hgamma := gammaHardyPhaseRate_tendsto_atTop.comp hscale
    have htwo : Tendsto (fun u : ℝ => 2 * gammaHardyPhaseRate (2 * Real.pi * u))
        atTop atTop :=
      hgamma.const_mul_atTop (by norm_num)
    have hshift := tendsto_atTop_add_const_right atTop
      (1 - 2 * gammaHardyPhaseRate 0) htwo
    convert hshift using 1 <;> funext u <;> ring

@[simp] theorem ccmArchimedeanFourierWeight_value_abs (xi : ℝ) :
    ccmArchimedeanFourierWeight.value |xi| = ccmArchimedeanFormWeight xi := rfl

def ccmArchimedeanFormMeasure : Measure ℝ :=
  volume.withDensity fun xi => (Real.toNNReal (ccmArchimedeanFormWeight xi) : ℝ≥0∞)

theorem measurable_ccmArchimedeanFormWeightNNReal :
    Measurable fun xi => Real.toNNReal (ccmArchimedeanFormWeight xi) :=
  measurable_ccmArchimedeanFormWeight.real_toNNReal

theorem coe_ccmArchimedeanFormWeightNNReal (xi : ℝ) :
    (Real.toNNReal (ccmArchimedeanFormWeight xi) : ℝ) = ccmArchimedeanFormWeight xi :=
  Real.coe_toNNReal _ (ccmArchimedeanFormWeight_pos xi).le

theorem volume_le_ccmArchimedeanFormMeasure :
    (volume : Measure ℝ) ≤ ccmArchimedeanFormMeasure := by
  calc
    (volume : Measure ℝ) = volume.withDensity 1 := withDensity_one.symm
    _ ≤ ccmArchimedeanFormMeasure := by
      apply withDensity_mono
      filter_upwards with xi
      change (1 : ℝ≥0∞) ≤
        (Real.toNNReal (ccmArchimedeanFormWeight xi) : ℝ≥0∞)
      have hreal : (1 : ℝ) ≤
          (Real.toNNReal (ccmArchimedeanFormWeight xi) : ℝ) := by
        rw [coe_ccmArchimedeanFormWeightNNReal]
        exact one_le_ccmArchimedeanFormWeight xi
      exact_mod_cast hreal

theorem ccmArchimedeanFormMeasure_absolutelyContinuous_volume :
    ccmArchimedeanFormMeasure ≪ (volume : Measure ℝ) :=
  withDensity_absolutelyContinuous _ _

abbrev CCMArchimedeanFourierL2 :=
  Lp (α := ℝ) ℂ 2 ccmArchimedeanFormMeasure

private theorem norm_sq_eq_integral_ccmArchimedeanFormMeasure
    (f : CCMArchimedeanFourierL2) :
    ‖f‖ ^ 2 = ∫ xi : ℝ, ‖(f : ℝ → ℂ) xi‖ ^ 2 ∂ccmArchimedeanFormMeasure := by
  have h2 := MeasureTheory.L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at h2
  have hpoint : ∀ xi : ℝ, inner ℂ ((f : ℝ → ℂ) xi) ((f : ℝ → ℂ) xi) =
      ((‖(f : ℝ → ℂ) xi‖ ^ 2 : ℝ) : ℂ) := by
    intro xi
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [hpoint] at h2
  rw [integral_complex_ofReal] at h2
  have h4 : ((‖f‖ ^ 2 : ℝ) : ℂ) =
      ((∫ xi : ℝ, ‖(f : ℝ → ℂ) xi‖ ^ 2 ∂ccmArchimedeanFormMeasure : ℝ) : ℂ) := by
    push_cast
    exact h2
  exact_mod_cast h4

theorem norm_sq_ccmArchimedeanFourierL2 (f : CCMArchimedeanFourierL2) :
    ‖f‖ ^ 2 =
      ∫ xi : ℝ, ccmArchimedeanFormWeight xi * ‖(f : ℝ → ℂ) xi‖ ^ 2 := by
  rw [norm_sq_eq_integral_ccmArchimedeanFormMeasure]
  unfold ccmArchimedeanFormMeasure
  rw [integral_withDensity_eq_integral_smul measurable_ccmArchimedeanFormWeightNNReal]
  apply integral_congr_ae
  filter_upwards with xi
  rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]

private def ccmArchimedeanWeightedToL2Real :
    CCMArchimedeanFourierL2 →L[ℝ] SoninL2 :=
  MeasureTheory.Lp.LpToLpOfMeasureLeSMul
    (c := (1 : ℝ≥0∞)) (by simp) (by simpa using volume_le_ccmArchimedeanFormMeasure)

theorem ccmArchimedeanWeightedToL2Real_coeFn (f : CCMArchimedeanFourierL2) :
    ccmArchimedeanWeightedToL2Real f =ᵐ[volume] f :=
  MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
    (c := (1 : ℝ≥0∞)) (by simp) (by simpa using volume_le_ccmArchimedeanFormMeasure) f

private def ccmArchimedeanWeightedToL2Linear :
    CCMArchimedeanFourierL2 →ₗ[ℂ] SoninL2 where
  toFun := ccmArchimedeanWeightedToL2Real
  map_add' := ccmArchimedeanWeightedToL2Real.map_add
  map_smul' c f := by
    apply MeasureTheory.Lp.ext
    have hsmul_in := (MeasureTheory.Lp.coeFn_smul c f).filter_mono
      (ae_mono volume_le_ccmArchimedeanFormMeasure)
    filter_upwards [ccmArchimedeanWeightedToL2Real_coeFn (c • f),
      ccmArchimedeanWeightedToL2Real_coeFn f, hsmul_in,
      MeasureTheory.Lp.coeFn_smul c (ccmArchimedeanWeightedToL2Real f)] with
        xi hcf hff hin hout
    change (ccmArchimedeanWeightedToL2Real (c • f) : ℝ → ℂ) xi =
      (c • ccmArchimedeanWeightedToL2Real f : SoninL2) xi
    rw [hcf, hout, hin]
    change c * f xi = c * (ccmArchimedeanWeightedToL2Real f : ℝ → ℂ) xi
    rw [hff]

def ccmArchimedeanWeightedToL2 : CCMArchimedeanFourierL2 →L[ℂ] SoninL2 :=
  LinearMap.mkContinuous ccmArchimedeanWeightedToL2Linear 1 fun f => by
    have hop : ‖ccmArchimedeanWeightedToL2Real‖ ≤ 1 := by
      unfold ccmArchimedeanWeightedToL2Real
      simpa using MeasureTheory.Lp.norm_LpToLpOfMeasureLeSMul_le
        (p := (2 : ℝ≥0∞)) (E := ℂ) (c := (1 : ℝ≥0∞))
        (μ := (volume : Measure ℝ)) (ν := ccmArchimedeanFormMeasure)
        (by simp) (by simpa using volume_le_ccmArchimedeanFormMeasure)
    calc
      ‖ccmArchimedeanWeightedToL2Linear f‖ = ‖ccmArchimedeanWeightedToL2Real f‖ := rfl
      _ ≤ ‖ccmArchimedeanWeightedToL2Real‖ * ‖f‖ :=
        ccmArchimedeanWeightedToL2Real.le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg f)

theorem ccmArchimedeanWeightedToL2_coeFn (f : CCMArchimedeanFourierL2) :
    ccmArchimedeanWeightedToL2 f =ᵐ[volume] f :=
  ccmArchimedeanWeightedToL2Real_coeFn f

theorem ccmArchimedeanWeightedToL2_injective :
    Function.Injective ccmArchimedeanWeightedToL2 := by
  intro f g hfg
  apply MeasureTheory.Lp.ext
  have hout : (ccmArchimedeanWeightedToL2 f : ℝ → ℂ) =ᵐ[volume]
      ccmArchimedeanWeightedToL2 g := by rw [hfg]
  have hcoe : (f : ℝ → ℂ) =ᵐ[volume] g :=
    (ccmArchimedeanWeightedToL2_coeFn f).symm.trans
      (hout.trans (ccmArchimedeanWeightedToL2_coeFn g))
  exact hcoe.filter_mono ccmArchimedeanFormMeasure_absolutelyContinuous_volume.ae_le

def ccmArchimedeanFourierToTime : CCMArchimedeanFourierL2 →L[ℂ] SoninL2 :=
  fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    ccmArchimedeanWeightedToL2

theorem ccmArchimedeanFourierToTime_injective :
    Function.Injective ccmArchimedeanFourierToTime := by
  intro f g hfg
  apply ccmArchimedeanWeightedToL2_injective
  exact fourierUnitary.symm.injective hfg

theorem fourierUnitary_ccmArchimedeanFourierToTime
    (f : CCMArchimedeanFourierL2) :
    fourierUnitary (ccmArchimedeanFourierToTime f) = ccmArchimedeanWeightedToL2 f :=
  fourierUnitary.apply_symm_apply _

def ccmArchimedeanSupportDefect (a : SuzukiPositiveAperture) :
    CCMArchimedeanFourierL2 →L[ℂ] SoninL2 :=
  (1 - indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)) ∘L
    ccmArchimedeanFourierToTime

/-- Exact complete archimedean form domain on the logarithmic aperture `[-a,a]`. -/
abbrev CCMArchimedeanFormDomain (a : SuzukiPositiveAperture) :=
  (ccmArchimedeanSupportDefect a).ker

def ccmArchimedeanFormEmbedding (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] SoninL2 :=
  ccmArchimedeanFourierToTime.domRestrict (ccmArchimedeanSupportDefect a).ker

theorem ccmArchimedeanFormEmbedding_injective (a : SuzukiPositiveAperture) :
    Function.Injective (ccmArchimedeanFormEmbedding a) := by
  intro f g hfg
  exact Subtype.ext (ccmArchimedeanFourierToTime_injective hfg)

theorem indicatorCutoff_ccmArchimedeanFormEmbedding
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
        (ccmArchimedeanFormEmbedding a f) = ccmArchimedeanFormEmbedding a f := by
  have hf := f.property
  rw [LinearMap.mem_ker] at hf
  change (1 - indicatorCutoff (centralInterval a.1)
    (measurableSet_centralInterval a.1)) (ccmArchimedeanFourierToTime f) = 0 at hf
  rw [sub_apply, one_apply_eq_self] at hf
  exact (sub_eq_zero.mp hf).symm

/-- Literal archimedean form embedding with codomain restricted to the physical aperture. -/
def ccmArchimedeanFormToAperture (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] suzukiApertureHilbert a :=
  (ccmArchimedeanFormEmbedding a).codRestrict (suzukiApertureHilbert a) fun f => by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    exact ⟨ccmArchimedeanFormEmbedding a f,
      indicatorCutoff_ccmArchimedeanFormEmbedding a f⟩

@[simp] theorem ccmArchimedeanFormToAperture_coe
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    (ccmArchimedeanFormToAperture a f : SoninL2) =
      ccmArchimedeanFormEmbedding a f := rfl

theorem ccmArchimedeanFormToAperture_injective (a : SuzukiPositiveAperture) :
    Function.Injective (ccmArchimedeanFormToAperture a) := by
  intro f g hfg
  exact ccmArchimedeanFormEmbedding_injective a (congrArg Subtype.val hfg)

theorem ccmArchimedeanFormEmbedding_mem_weightUnitBall_of_mem_closedBall
    (a : SuzukiPositiveAperture) {f : CCMArchimedeanFormDomain a}
    (hf : f ∈ Metric.closedBall 0 1) :
    ccmArchimedeanFormEmbedding a f ∈
      ccmFourierWeightUnitBall ccmArchimedeanFourierWeight
        ⟨-a.1, a.1, by linarith [a.property]⟩ := by
  refine ⟨indicatorCutoff_ccmArchimedeanFormEmbedding a f, ?_, ?_⟩
  · have hfint : Integrable (fun xi : ℝ => ‖(f.1 : ℝ → ℂ) xi‖ ^ 2)
        ccmArchimedeanFormMeasure :=
      (MeasureTheory.Lp.memLp f.1).integrable_norm_pow (by norm_num)
    have hweighted : Integrable
        (fun xi : ℝ => Real.toNNReal (ccmArchimedeanFormWeight xi) •
          ‖(f.1 : ℝ → ℂ) xi‖ ^ 2) volume :=
      (integrable_withDensity_iff_integrable_smul
        measurable_ccmArchimedeanFormWeightNNReal).mp hfint
    refine hweighted.congr ?_
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn f.1] with xi hxi
    unfold ccmFourierWeightDensity
    simp_rw [ccmArchimedeanFourierWeight_value_abs]
    change Real.toNNReal (ccmArchimedeanFormWeight xi) • ‖f.1 xi‖ ^ 2 =
      ccmArchimedeanFormWeight xi *
        ‖fourierUnitary (ccmArchimedeanFourierToTime f.1) xi‖ ^ 2
    rw [fourierUnitary_ccmArchimedeanFourierToTime, hxi,
      NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]
  · unfold ccmFourierWeightMoment ccmFourierWeightDensity
    simp_rw [ccmArchimedeanFourierWeight_value_abs]
    change (∫ xi : ℝ, ccmArchimedeanFormWeight xi *
        ‖fourierUnitary (ccmArchimedeanFourierToTime f.1) xi‖ ^ 2) ≤ 1
    rw [fourierUnitary_ccmArchimedeanFourierToTime]
    have heq : (∫ xi : ℝ, ccmArchimedeanFormWeight xi *
        ‖(ccmArchimedeanWeightedToL2 f.1 : ℝ → ℂ) xi‖ ^ 2) = ‖f‖ ^ 2 := by
      calc
        _ = ∫ xi : ℝ, ccmArchimedeanFormWeight xi * ‖(f.1 : ℝ → ℂ) xi‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [ccmArchimedeanWeightedToL2_coeFn f.1] with xi hxi
          rw [hxi]
        _ = ‖f.1‖ ^ 2 := (norm_sq_ccmArchimedeanFourierL2 f.1).symm
        _ = ‖f‖ ^ 2 := rfl
    rw [heq]
    rw [Metric.mem_closedBall, dist_zero_right] at hf
    nlinarith [norm_nonneg f]

theorem isCompactOperator_ccmArchimedeanFormEmbedding (a : SuzukiPositiveAperture) :
    IsCompactOperator (ccmArchimedeanFormEmbedding a) := by
  let I : SuzukiBoundedInterval := ⟨-a.1, a.1, by linarith [a.property]⟩
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (ccmArchimedeanFormEmbedding a).toLinearMap zero_lt_one).2
  refine ⟨closure (ccmFourierWeightUnitBall ccmArchimedeanFourierWeight I),
    isCompact_closure_ccmFourierWeightUnitBall ccmArchimedeanFourierWeight I, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact subset_closure
    (ccmArchimedeanFormEmbedding_mem_weightUnitBall_of_mem_closedBall a hf)

theorem isCompactOperator_ccmArchimedeanFormToAperture (a : SuzukiPositiveAperture) :
    IsCompactOperator (ccmArchimedeanFormToAperture a) := by
  apply (isCompactOperator_ccmArchimedeanFormEmbedding a).codRestrict
  · exact fun f => (ccmArchimedeanFormToAperture a f).property
  · exact (inferInstance : (suzukiApertureHilbert a).HasOrthogonalProjection).isClosed

/-- Exact decomposition of the source archimedean spectral density on the form domain. -/
theorem ccmArchimedean_form_eq_domainNorm_add_scalar
    (f : CCMArchimedeanFourierL2) :
    ∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
        ‖(f : ℝ → ℂ) xi‖ ^ 2 =
      ‖f‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1) *
        ‖ccmArchimedeanWeightedToL2 f‖ ^ 2 := by
  let c : ℝ := 2 * gammaHardyPhaseRate 0 - 1
  have heven (xi : ℝ) :
      gammaHardyPhaseRate (2 * Real.pi * xi) =
        gammaHardyPhaseRate (2 * Real.pi * |xi|) := by
    by_cases hxi : 0 ≤ xi
    · rw [abs_of_nonneg hxi]
    · have hneg : xi < 0 := lt_of_not_ge hxi
      have habs : 2 * Real.pi * |xi| = -(2 * Real.pi * xi) := by
        rw [abs_of_neg hneg]
        ring
      rw [habs]
      exact (gammaHardyPhaseRate_neg (2 * Real.pi * xi)).symm
  have hpoint (xi : ℝ) :
      2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(f : ℝ → ℂ) xi‖ ^ 2 =
        ccmArchimedeanFormWeight xi * ‖(f : ℝ → ℂ) xi‖ ^ 2 +
          c * ‖(f : ℝ → ℂ) xi‖ ^ 2 := by
    rw [heven]
    unfold ccmArchimedeanFormWeight c
    ring
  have hfint : Integrable (fun xi : ℝ => ‖(f : ℝ → ℂ) xi‖ ^ 2)
      ccmArchimedeanFormMeasure :=
    (MeasureTheory.Lp.memLp f).integrable_norm_pow (by norm_num)
  have hweighted : Integrable
      (fun xi : ℝ => ccmArchimedeanFormWeight xi * ‖(f : ℝ → ℂ) xi‖ ^ 2) volume := by
    have h := (integrable_withDensity_iff_integrable_smul
      measurable_ccmArchimedeanFormWeightNNReal).mp hfint
    refine h.congr ?_
    filter_upwards with xi
    rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]
  have hplain : Integrable (fun xi : ℝ => ‖(f : ℝ → ℂ) xi‖ ^ 2) volume :=
    ((MeasureTheory.Lp.memLp (ccmArchimedeanWeightedToL2 f)).integrable_norm_pow
      (by norm_num)).congr (by
        filter_upwards [ccmArchimedeanWeightedToL2_coeFn f] with xi hxi
        rw [hxi])
  rw [show (fun xi : ℝ => 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
      ‖(f : ℝ → ℂ) xi‖ ^ 2) =
      (fun xi : ℝ => ccmArchimedeanFormWeight xi * ‖(f : ℝ → ℂ) xi‖ ^ 2) +
        fun xi : ℝ => c * ‖(f : ℝ → ℂ) xi‖ ^ 2 by
      funext xi
      exact hpoint xi]
  change (∫ xi : ℝ, ccmArchimedeanFormWeight xi * ‖(f : ℝ → ℂ) xi‖ ^ 2 +
      c * ‖(f : ℝ → ℂ) xi‖ ^ 2) = _
  rw [integral_add hweighted (hplain.const_mul c), integral_const_mul,
    ← norm_sq_ccmArchimedeanFourierL2 f]
  have hL2 : (∫ xi : ℝ, ‖(f : ℝ → ℂ) xi‖ ^ 2) =
      ‖ccmArchimedeanWeightedToL2 f‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn f] with xi hxi
    rw [hxi]
  rw [hL2]

end RHTower
