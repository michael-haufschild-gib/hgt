import GaloisForLFunctions.RHTower.SuzukiHlogCompactEmbedding
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Set
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

theorem measurable_suzukiLogWeight : Measurable suzukiLogWeight := by
  unfold suzukiLogWeight
  exact measurable_const.add ((Real.measurable_log.comp measurable_abs).max measurable_const)

def suzukiHlogMeasure : Measure ℝ :=
  volume.withDensity fun ξ => (Real.toNNReal (suzukiLogWeight ξ) : ℝ≥0∞)

theorem measurable_suzukiLogWeightNNReal :
    Measurable fun ξ => Real.toNNReal (suzukiLogWeight ξ) :=
  measurable_suzukiLogWeight.real_toNNReal

theorem coe_suzukiLogWeightNNReal (ξ : ℝ) :
    (Real.toNNReal (suzukiLogWeight ξ) : ℝ) = suzukiLogWeight ξ :=
  Real.coe_toNNReal _ (suzukiLogWeight_nonneg ξ)

theorem volume_le_suzukiHlogMeasure :
    (volume : Measure ℝ) ≤ suzukiHlogMeasure := by
  calc
    (volume : Measure ℝ) = volume.withDensity 1 := withDensity_one.symm
    _ ≤ suzukiHlogMeasure := by
      apply withDensity_mono
      filter_upwards with ξ
      change (1 : ℝ≥0∞) ≤ (Real.toNNReal (suzukiLogWeight ξ) : ℝ≥0∞)
      have hreal : (1 : ℝ) ≤ (Real.toNNReal (suzukiLogWeight ξ) : ℝ) := by
        rw [coe_suzukiLogWeightNNReal]
        exact one_le_suzukiLogWeight ξ
      exact_mod_cast hreal

theorem suzukiHlogMeasure_absolutelyContinuous_volume :
    suzukiHlogMeasure ≪ (volume : Measure ℝ) :=
  withDensity_absolutelyContinuous _ _

abbrev SuzukiHlogFourierL2 := Lp (α := ℝ) ℂ 2 suzukiHlogMeasure

private theorem norm_sq_eq_integral_measure (μ : Measure ℝ) (f : Lp (α := ℝ) ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 ∂μ := by
  have h2 := MeasureTheory.L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at h2
  have h3 : ∀ x : ℝ, inner ℂ ((f : ℝ → ℂ) x) ((f : ℝ → ℂ) x) =
      ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [h3] at h2
  rw [integral_complex_ofReal] at h2
  have h4 : ((‖f‖ ^ 2 : ℝ) : ℂ) =
      ((∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    push_cast
    exact h2
  exact_mod_cast h4

theorem norm_sq_suzukiHlogFourierL2 (f : SuzukiHlogFourierL2) :
    ‖f‖ ^ 2 = ∫ ξ : ℝ, suzukiLogWeight ξ * ‖(f : ℝ → ℂ) ξ‖ ^ 2 := by
  rw [norm_sq_eq_integral_measure suzukiHlogMeasure f]
  unfold suzukiHlogMeasure
  rw [integral_withDensity_eq_integral_smul measurable_suzukiLogWeightNNReal]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [NNReal.smul_def, smul_eq_mul, coe_suzukiLogWeightNNReal]

private def suzukiHlogWeightedToL2Real : SuzukiHlogFourierL2 →L[ℝ] SoninL2 :=
  MeasureTheory.Lp.LpToLpOfMeasureLeSMul
    (c := (1 : ℝ≥0∞)) (by simp) (by simpa using volume_le_suzukiHlogMeasure)

theorem suzukiHlogWeightedToL2Real_coeFn (f : SuzukiHlogFourierL2) :
    suzukiHlogWeightedToL2Real f =ᵐ[volume] f :=
  MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
    (c := (1 : ℝ≥0∞)) (by simp) (by simpa using volume_le_suzukiHlogMeasure) f

private def suzukiHlogWeightedToL2Linear : SuzukiHlogFourierL2 →ₗ[ℂ] SoninL2 where
  toFun := suzukiHlogWeightedToL2Real
  map_add' := suzukiHlogWeightedToL2Real.map_add
  map_smul' c f := by
    apply MeasureTheory.Lp.ext
    have hsmul_in := (MeasureTheory.Lp.coeFn_smul c f).filter_mono
      (ae_mono volume_le_suzukiHlogMeasure)
    filter_upwards [suzukiHlogWeightedToL2Real_coeFn (c • f),
      suzukiHlogWeightedToL2Real_coeFn f, hsmul_in,
      MeasureTheory.Lp.coeFn_smul c (suzukiHlogWeightedToL2Real f)] with ξ hcf hff hin hout
    change (suzukiHlogWeightedToL2Real (c • f) : ℝ → ℂ) ξ =
      (c • suzukiHlogWeightedToL2Real f : SoninL2) ξ
    rw [hcf, hout, hin]
    change c * f ξ = c * suzukiHlogWeightedToL2Real f ξ
    rw [hff]

def suzukiHlogWeightedToL2 : SuzukiHlogFourierL2 →L[ℂ] SoninL2 :=
  LinearMap.mkContinuous suzukiHlogWeightedToL2Linear 1 fun f => by
    have hop : ‖suzukiHlogWeightedToL2Real‖ ≤ 1 := by
      unfold suzukiHlogWeightedToL2Real
      simpa using MeasureTheory.Lp.norm_LpToLpOfMeasureLeSMul_le
        (p := (2 : ℝ≥0∞)) (E := ℂ) (c := (1 : ℝ≥0∞))
        (μ := (volume : Measure ℝ)) (ν := suzukiHlogMeasure)
        (by simp) (by simpa using volume_le_suzukiHlogMeasure)
    calc
      ‖suzukiHlogWeightedToL2Linear f‖ = ‖suzukiHlogWeightedToL2Real f‖ := rfl
      _ ≤ ‖suzukiHlogWeightedToL2Real‖ * ‖f‖ :=
        suzukiHlogWeightedToL2Real.le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg f)

theorem suzukiHlogWeightedToL2_coeFn (f : SuzukiHlogFourierL2) :
    suzukiHlogWeightedToL2 f =ᵐ[volume] f :=
  suzukiHlogWeightedToL2Real_coeFn f

theorem suzukiHlogWeightedToL2_injective :
    Function.Injective suzukiHlogWeightedToL2 := by
  intro f g hfg
  apply MeasureTheory.Lp.ext
  have hout : (suzukiHlogWeightedToL2 f : ℝ → ℂ) =ᵐ[volume]
      suzukiHlogWeightedToL2 g := by rw [hfg]
  have hcoe : (f : ℝ → ℂ) =ᵐ[volume] g :=
    (suzukiHlogWeightedToL2_coeFn f).symm.trans
      (hout.trans (suzukiHlogWeightedToL2_coeFn g))
  exact hcoe.filter_mono suzukiHlogMeasure_absolutelyContinuous_volume.ae_le

def suzukiHlogFourierToTime : SuzukiHlogFourierL2 →L[ℂ] SoninL2 :=
  fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L suzukiHlogWeightedToL2

theorem suzukiHlogFourierToTime_injective :
    Function.Injective suzukiHlogFourierToTime := by
  intro f g hfg
  apply suzukiHlogWeightedToL2_injective
  exact fourierUnitary.symm.injective hfg

theorem fourierUnitary_suzukiHlogFourierToTime (f : SuzukiHlogFourierL2) :
    fourierUnitary (suzukiHlogFourierToTime f) = suzukiHlogWeightedToL2 f :=
  fourierUnitary.apply_symm_apply _

def suzukiHlogSupportDefect (a : SuzukiPositiveAperture) :
    SuzukiHlogFourierL2 →L[ℂ] SoninL2 :=
  (1 - indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)) ∘L
    suzukiHlogFourierToTime

/-- Literal complete `H^log(-a,a)` form domain: weighted Fourier `L²` vectors whose inverse
Fourier transforms vanish off the aperture. -/
abbrev SuzukiHlogFormDomain (a : SuzukiPositiveAperture) :=
  (suzukiHlogSupportDefect a).ker

def suzukiHlogFormEmbedding (a : SuzukiPositiveAperture) :
    SuzukiHlogFormDomain a →L[ℂ] SoninL2 :=
  suzukiHlogFourierToTime.domRestrict (suzukiHlogSupportDefect a).ker

theorem suzukiHlogFormEmbedding_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiHlogFormEmbedding a) := by
  intro f g hfg
  exact Subtype.ext (suzukiHlogFourierToTime_injective hfg)

theorem indicatorCutoff_suzukiHlogFormEmbedding
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
        (suzukiHlogFormEmbedding a f) = suzukiHlogFormEmbedding a f := by
  have hf := f.property
  rw [LinearMap.mem_ker] at hf
  change (1 - indicatorCutoff (centralInterval a.1)
    (measurableSet_centralInterval a.1)) (suzukiHlogFourierToTime f) = 0 at hf
  rw [sub_apply, one_apply_eq_self] at hf
  change indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (suzukiHlogFourierToTime f.1) = suzukiHlogFourierToTime f.1
  exact (sub_eq_zero.mp hf).symm

theorem integrable_suzukiHlogDensity_formEmbedding
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    Integrable (suzukiHlogDensity (suzukiHlogFormEmbedding a f)) := by
  have hfint : Integrable (fun ξ : ℝ => ‖(f.1 : ℝ → ℂ) ξ‖ ^ 2)
      suzukiHlogMeasure :=
    (MeasureTheory.Lp.memLp f.1).integrable_norm_pow (by norm_num)
  have hweighted : Integrable
      (fun ξ : ℝ => Real.toNNReal (suzukiLogWeight ξ) • ‖(f.1 : ℝ → ℂ) ξ‖ ^ 2)
      volume :=
    (integrable_withDensity_iff_integrable_smul measurable_suzukiLogWeightNNReal).mp hfint
  have hcoe : (fun ξ : ℝ => (suzukiHlogWeightedToL2 f.1 : ℝ → ℂ) ξ) =ᵐ[volume]
      fun ξ => (f.1 : ℝ → ℂ) ξ := suzukiHlogWeightedToL2_coeFn f.1
  refine hweighted.congr ?_
  filter_upwards [hcoe] with ξ hξ
  unfold suzukiHlogDensity
  change Real.toNNReal (suzukiLogWeight ξ) • ‖f.1 ξ‖ ^ 2 =
    suzukiLogWeight ξ *
      ‖fourierUnitary (suzukiHlogFourierToTime f.1) ξ‖ ^ 2
  rw [fourierUnitary_suzukiHlogFourierToTime]
  rw [hξ, NNReal.smul_def, smul_eq_mul, coe_suzukiLogWeightNNReal]

theorem suzukiHlogMoment_formEmbedding_eq_norm_sq
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    suzukiHlogMoment (suzukiHlogFormEmbedding a f) = ‖f‖ ^ 2 := by
  rw [suzukiHlogMoment]
  change ∫ ξ : ℝ, suzukiHlogDensity (suzukiHlogFormEmbedding a f) ξ = ‖f.1‖ ^ 2
  rw [norm_sq_suzukiHlogFourierL2 f.1]
  apply integral_congr_ae
  filter_upwards [suzukiHlogWeightedToL2_coeFn f.1] with ξ hξ
  unfold suzukiHlogDensity
  change suzukiLogWeight ξ *
      ‖fourierUnitary (suzukiHlogFourierToTime f.1) ξ‖ ^ 2 =
    suzukiLogWeight ξ * ‖f.1 ξ‖ ^ 2
  rw [fourierUnitary_suzukiHlogFourierToTime, hξ]

theorem suzukiHlogFormEmbedding_closedBall_subset_unitBall
    (a : SuzukiPositiveAperture) :
    suzukiHlogFormEmbedding a '' Metric.closedBall 0 1 ⊆
      suzukiHlogCentralUnitBall a := by
  rintro _ ⟨f, hf, rfl⟩
  refine ⟨indicatorCutoff_suzukiHlogFormEmbedding a f,
    integrable_suzukiHlogDensity_formEmbedding a f, ?_⟩
  rw [suzukiHlogMoment_formEmbedding_eq_norm_sq]
  rw [Metric.mem_closedBall, dist_zero_right] at hf
  nlinarith [norm_nonneg f]

theorem isCompactOperator_suzukiHlogFormEmbedding (a : SuzukiPositiveAperture) :
    IsCompactOperator (suzukiHlogFormEmbedding a) := by
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (suzukiHlogFormEmbedding a).toLinearMap zero_lt_one).2
  exact ⟨closure (suzukiHlogCentralUnitBall a),
    isCompact_closure_suzukiHlogCentralUnitBall a,
    (suzukiHlogFormEmbedding_closedBall_subset_unitBall a).trans subset_closure⟩

end RHTower
