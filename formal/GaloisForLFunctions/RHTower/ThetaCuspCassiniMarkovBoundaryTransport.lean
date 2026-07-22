import GaloisForLFunctions.RHTower.CompletedSeamCompactThorinExponentCapstone
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodAtomicNondivisibility
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Euler-boundary compact Markov transport to the centered RH seam

The genuine theta response is available at the Euler-safe Cassini boundary `u = 0`, whereas the
RH-complete moment germ is centered at `u = 1`. This module proves that source comparison need
not be repeated at the center. If one finite positive compact measure represents the theta
boundary response through the shifted kernel `(1 - x * (u - 1))⁻¹`, the same measure analytically
transports along the unconditionally zero-free Cassini segment from `0` to `1`. It then represents
the completed-seam Markov germ and the existing capstone proves RH.

Positivity is still an upstream producer obligation. The theorem removes only the independent
global comparison/continuation obligation.
-/

open Complex Filter MeasureTheory Metric Set Topology

namespace RHTower

noncomputable section

/-- Source-side predecessor: one compact positive measure represents the genuine inward theta
response near the Euler-safe Cassini boundary, already in the centered reciprocal-square
coordinate. -/
def ThetaCuspCassiniCompactMarkovBoundaryRepresentation : Prop :=
  ∃ (μ : Measure ℝ) (B : ℝ),
    IsFiniteMeasure μ ∧
    0 < B ∧ B < 1 / 2 ∧
    (∀ᵐ x : ℝ ∂μ, 0 ≤ x ∧ |x| ≤ B) ∧
    (fun u : ℝ => compactMarkovTransform μ ((u : ℂ) - 1)) =ᶠ[
      nhdsWithin 0 (Ioi 0)] thetaCuspCassiniInwardCoordinateResponse

private theorem isCompact_segment_zero_one :
    IsCompact (segment ℝ (0 : ℂ) 1) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

/-- The canonical Cassini source has no zero on the closed transport segment from the Euler-safe
boundary to the functional-equation center. -/
theorem xiSquaredSeamCassiniSource_ne_zero_of_mem_segment_zero_one
    {u : ℂ} (hu : u ∈ segment ℝ (0 : ℂ) 1) :
    xiSquaredSeamCassiniSource u ≠ 0 := by
  rw [segment_eq_image] at hu
  rcases hu with ⟨t, ht, rfl⟩
  simp only [smul_zero, zero_add, Complex.real_smul, mul_one]
  rcases eq_or_lt_of_le ht.2 with ht1 | ht1
  · subst t
    simpa using xiSquaredSeamCassiniSource_one_ne
  · have honeSub : 0 ≤ 1 - t := by linarith
    let r : ℝ := Real.sqrt (1 - t)
    have hr : 0 < r := Real.sqrt_pos.2 (sub_pos.mpr ht1)
    have hrsq : r ^ 2 = 1 - t := Real.sq_sqrt honeSub
    have hcoord : 1 + (-((r : ℂ) * I)) ^ 2 = (t : ℂ) := by
      calc
        1 + (-((r : ℂ) * I)) ^ 2 = 1 - (r : ℂ) ^ 2 := by
          rw [neg_sq, mul_pow, I_sq]
          ring
        _ = (t : ℂ) := by
          have hreal : 1 - r ^ 2 = t := by linarith [hrsq]
          exact_mod_cast hreal
    rw [← hcoord, xiSquaredSeamCassiniSource_one_add_sq]
    exact XiC_neg_imaginaryAxis_ne_zero hr

private theorem analyticOnNhd_shifted_compactMarkovTransform
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 < B) (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B) :
    AnalyticOnNhd ℂ (fun u : ℂ => compactMarkovTransform μ (u - 1))
      (Metric.ball 1 (1 / (2 * B))) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro u hu
  have huradius : ‖u - 1‖ < 1 / (2 * B) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hu
  have hshift : HasDerivAt (fun w : ℂ => w - 1) 1 u := by
    simpa using (hasDerivAt_id u).sub_const 1
  have hmarkov := hasDerivAt_compactMarkovKernelMoment μ hB hbound 0 huradius
  exact (hmarkov.comp u hshift).differentiableAt.differentiableWithinAt

private theorem analyticOnNhd_negTwoCassiniLogDeriv :
    AnalyticOnNhd ℂ (fun u : ℂ =>
      -2 * logDeriv xiSquaredSeamCassiniSource u)
      {u : ℂ | xiSquaredSeamCassiniSource u ≠ 0} := by
  intro u hu
  have hsource : AnalyticAt ℂ xiSquaredSeamCassiniSource u :=
    differentiable_xiSquaredSeamCassiniSource.analyticAt u
  have hlog : AnalyticAt ℂ (logDeriv xiSquaredSeamCassiniSource) u := by
    rw [show logDeriv xiSquaredSeamCassiniSource = fun z =>
      deriv xiSquaredSeamCassiniSource z / xiSquaredSeamCassiniSource z by rfl]
    exact hsource.deriv.div hsource hu
  exact analyticAt_const.mul hlog

/-- A compact positive Markov identity at the genuine theta boundary transports to the centered
completed-seam Markov germ, preserving the supplied measure rather than merely producing some
existential witness. -/
theorem completedSeamMomentGerm_eventuallyEq_compactMarkovTransform_of_thetaBoundary
    {μ : Measure ℝ} {B : ℝ}
    (hfinite : IsFiniteMeasure μ)
    (hB : 0 < B) (hBhalf : B < 1 / 2)
    (hsupport : ∀ᵐ x : ℝ ∂μ, 0 ≤ x ∧ |x| ≤ B)
    (hboundary :
      (fun u : ℝ => compactMarkovTransform μ ((u : ℂ) - 1)) =ᶠ[
        nhdsWithin 0 (Ioi 0)] thetaCuspCassiniInwardCoordinateResponse) :
    completedSeamMomentGerm =ᶠ[nhds 0] compactMarkovTransform μ := by
  letI : IsFiniteMeasure μ := hfinite
  have hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B := hsupport.mono fun _ hx => hx.2
  let radius : ℝ := 1 / (2 * B)
  have hradius : 1 < radius := by
    dsimp only [radius]
    rw [lt_div_iff₀ (by positivity : 0 < 2 * B)]
    nlinarith
  let S : Set ℂ := segment ℝ (0 : ℂ) 1
  let W : Set ℂ :=
    {u : ℂ | xiSquaredSeamCassiniSource u ≠ 0} ∩ Metric.ball 1 radius
  have hWopen : IsOpen W := by
    apply IsOpen.inter
    · change IsOpen (xiSquaredSeamCassiniSource ⁻¹' {0}ᶜ)
      exact isOpen_ne.preimage differentiable_xiSquaredSeamCassiniSource.continuous
    · exact Metric.isOpen_ball
  have hScompact : IsCompact S := isCompact_segment_zero_one
  have hSW : S ⊆ W := by
    intro u hu
    refine ⟨xiSquaredSeamCassiniSource_ne_zero_of_mem_segment_zero_one hu, ?_⟩
    rw [Metric.mem_ball]
    have hclosed := segment_subset_closedBall_right (0 : ℂ) 1 hu
    rw [Metric.mem_closedBall] at hclosed
    have hdist : dist (0 : ℂ) 1 = 1 := by norm_num
    rw [hdist] at hclosed
    exact hclosed.trans_lt hradius
  obtain ⟨δ, hδ, hδW⟩ := hScompact.exists_cthickening_subset_open hWopen hSW
  let V : Set ℂ := Metric.thickening δ S
  have hVW : V ⊆ W :=
    (Metric.thickening_subset_cthickening δ S).trans hδW
  have hVopen : IsOpen V := Metric.isOpen_thickening
  have hVconvex : Convex ℝ V := (convex_segment (0 : ℂ) 1).thickening δ
  have hzeroS : (0 : ℂ) ∈ S := left_mem_segment ℝ 0 1
  have honeS : (1 : ℂ) ∈ S := right_mem_segment ℝ 0 1
  have hzeroV : (0 : ℂ) ∈ V := Metric.self_subset_thickening hδ S hzeroS
  have honeV : (1 : ℂ) ∈ V := Metric.self_subset_thickening hδ S honeS
  let F : ℂ → ℂ := fun u => compactMarkovTransform μ (u - 1)
  let H : ℂ → ℂ := fun u => -2 * logDeriv xiSquaredSeamCassiniSource u
  have hFanalytic : AnalyticOnNhd ℂ F V := by
    apply (analyticOnNhd_shifted_compactMarkovTransform μ hB hbound).mono
    intro u hu
    exact (hVW hu).2
  have hHanalytic : AnalyticOnNhd ℂ H V := by
    apply analyticOnNhd_negTwoCassiniLogDeriv.mono
    intro u hu
    exact (hVW hu).1
  have hFextension : IsThetaCuspCassiniInwardAnalyticExtension F := by
    refine ⟨hFanalytic 0 hzeroV, ?_⟩
    exact hboundary
  have hlocal : H =ᶠ[nhds 0] F :=
    negTwoCassiniLogDeriv_eventuallyEq_momentGerm.trans
      hFextension.eventuallyEq_momentGerm.symm
  have hglobal : Set.EqOn H F V :=
    hHanalytic.eqOn_of_preconnected_of_eventuallyEq hFanalytic
      hVconvex.isPreconnected hzeroV hlocal
  have hnearOne : H =ᶠ[nhds 1] F :=
    hglobal.eventuallyEq_of_mem (hVopen.mem_nhds honeV)
  have hshiftTendsto : Tendsto (fun z : ℂ => 1 + z) (nhds 0) (nhds 1) := by
    have hconst : Tendsto (fun _ : ℂ => (1 : ℂ)) (nhds 0) (nhds 1) :=
      tendsto_const_nhds
    have hid : Tendsto (fun z : ℂ => z) (nhds 0) (nhds 0) :=
      continuousAt_id
    simpa using hconst.add hid
  have hshift : (fun z : ℂ => H (1 + z)) =ᶠ[nhds 0]
      fun z : ℂ => compactMarkovTransform μ z := by
    filter_upwards [hshiftTendsto.eventually hnearOne] with z hz
    simpa only [F, add_sub_cancel_left] using hz
  exact completedSeamMomentGerm_eventuallyEq_negTwoCassiniShiftLogDeriv.trans hshift

/-- Existential wrapper around the measure-preserving boundary transport theorem. -/
theorem primeArchCompactMarkovGermRepresentation_of_thetaBoundary
    (hrep : ThetaCuspCassiniCompactMarkovBoundaryRepresentation) :
    PrimeArchCompactMarkovGermRepresentation := by
  obtain ⟨μ, B, hfinite, hB, hBhalf, hsupport, hboundary⟩ := hrep
  refine ⟨μ, B, hfinite, hB, hsupport, ?_⟩
  exact completedSeamMomentGerm_eventuallyEq_compactMarkovTransform_of_thetaBoundary
    hfinite hB hBhalf hsupport hboundary

/-- Zeroth-order extraction retains the concrete witness: a centered Markov germ has total real
mass equal to the canonical zeroth prime--archimedean moment. -/
theorem normalizedPrimeArchMoment_zero_eq_measureReal_univ_of_compactMarkovGerm
    (μ : Measure ℝ)
    (hgerm : completedSeamMomentGerm =ᶠ[nhds 0] compactMarkovTransform μ) :
    normalizedPrimeArchMoment 0 = μ.real Set.univ := by
  have hzero := hgerm.self_of_nhds
  have hsource : completedSeamMomentGerm 0 =
      (normalizedPrimeArchMoment 0 : ℂ) := by
    rw [completedSeamMomentGerm_eq_tsum, tsum_eq_single 0]
    · norm_num
    · intro b hb
      simp [hb]
  have hmarkov : compactMarkovTransform μ 0 = (μ.real Set.univ : ℂ) := by
    rw [compactMarkovTransform, compactMarkovKernelMoment]
    simp [MeasureTheory.integral_const]
  rw [hsource, hmarkov] at hzero
  exact Complex.ofReal_inj.mp hzero

/-- Right-to-left capstone: a local Euler-boundary compact Markov representation implies RH. -/
theorem riemannHypothesis_of_thetaCuspCassiniCompactMarkovBoundaryRepresentation
    (hrep : ThetaCuspCassiniCompactMarkovBoundaryRepresentation) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchCompactMarkovGermRepresentation
    (primeArchCompactMarkovGermRepresentation_of_thetaBoundary hrep)

/-! ## Explicit reciprocal-likelihood candidate -/

/-- Reciprocal square-gap coordinate on the fixed theta likelihood carrier. -/
def thetaCuspLikelihoodReciprocalGap (r : ℝ) : ℝ := r⁻¹

theorem measurable_thetaCuspLikelihoodReciprocalGap :
    Measurable thetaCuspLikelihoodReciprocalGap := by
  exact measurable_inv

private theorem measurableSet_thetaCuspReciprocalSupport :
    MeasurableSet {x : ℝ | 0 ≤ x ∧ |x| ≤ 1 / 3} := by
  exact (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_le measurable_id.abs measurable_const)

private theorem measurableSet_thetaCuspReciprocalGapSupport :
    MeasurableSet {r : ℝ |
      0 ≤ thetaCuspLikelihoodReciprocalGap r ∧
        |thetaCuspLikelihoodReciprocalGap r| ≤ 1 / 3} := by
  exact measurableSet_thetaCuspReciprocalSupport.preimage
    measurable_thetaCuspLikelihoodReciprocalGap

/-- Exponentially tilt at the modular seam, include the first-atom mass at zero, then push the
fixed likelihood carrier through reciprocal square gaps. -/
def thetaCuspCassiniReciprocalLikelihoodMeasure : Measure ℝ :=
  Measure.map thetaCuspLikelihoodReciprocalGap
    (thetaCuspLikelihoodSeamTiltedMeasure (thetaCuspLikelihoodCoordinate 0))

/-- Every positive likelihood tilt has finite total mass. -/
theorem thetaCuspHigherLikelihoodTiltedMeasure_finite
    {B : ℝ} (hB : 0 < B) :
    IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure B) := by
  have h := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 0 hB
  simp only [pow_zero] at h
  exact (integrable_const_iff.mp h).resolve_left one_ne_zero

/-- Adding the first-atom Dirac mass preserves finiteness. -/
theorem thetaCuspLikelihoodSeamTiltedMeasure_finite
    {B : ℝ} (hB : 0 < B) :
    IsFiniteMeasure (thetaCuspLikelihoodSeamTiltedMeasure B) := by
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure B) :=
    thetaCuspHigherLikelihoodTiltedMeasure_finite hB
  rw [thetaCuspLikelihoodSeamTiltedMeasure]
  infer_instance

private theorem ae_three_le_thetaCuspAtomLikelihoodSpectralMeasure
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ r ∂thetaCuspAtomLikelihoodSpectralMeasure n, 3 ≤ r := by
  have hgap : (3 : ℝ) ≤ thetaCuspLikelihoodGap n := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    unfold thetaCuspLikelihoodGap
    nlinarith
  rw [thetaCuspAtomLikelihoodSpectralMeasure, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff measurableSet_Ici]
    exact hgap
  · apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hgap.trans hr.le

private theorem ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure :
    ∀ᵐ r ∂thetaCuspHigherLikelihoodSpectralMeasure, 3 ≤ r := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure, Measure.ae_sum_iff]
  intro k
  exact ae_three_le_thetaCuspAtomLikelihoodSpectralMeasure (by omega)

/-- Exponential tilting preserves the sharp lower support edge `3`. -/
theorem ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure (B : ℝ) :
    ∀ᵐ r ∂thetaCuspHigherLikelihoodTiltedMeasure B, 3 ≤ r := by
  rw [thetaCuspHigherLikelihoodTiltedMeasure,
    ae_withDensity_iff
      (measurable_thetaCuspHigherLikelihoodTiltDensity B).coe_nnreal_ennreal]
  filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with r hr _
  exact hr

private theorem reciprocalGap_mem_zero_oneThird_of_zero_or_three_le
    {r : ℝ} (hr : r = 0 ∨ 3 ≤ r) :
    0 ≤ thetaCuspLikelihoodReciprocalGap r ∧
      |thetaCuspLikelihoodReciprocalGap r| ≤ 1 / 3 := by
  rcases hr with rfl | hr
  · norm_num [thetaCuspLikelihoodReciprocalGap]
  · have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
    rw [thetaCuspLikelihoodReciprocalGap, abs_of_pos (inv_pos.mpr hrpos)]
    constructor
    · exact (inv_pos.mpr hrpos).le
    · simpa only [one_div] using
        (inv_le_inv₀ hrpos (by norm_num : (0 : ℝ) < 3)).2 hr

private theorem ae_reciprocalGap_mem_zero_oneThird_seamTilted :
    ∀ᵐ r ∂thetaCuspLikelihoodSeamTiltedMeasure
        (thetaCuspLikelihoodCoordinate 0),
      0 ≤ thetaCuspLikelihoodReciprocalGap r ∧
        |thetaCuspLikelihoodReciprocalGap r| ≤ 1 / 3 := by
  rw [thetaCuspLikelihoodSeamTiltedMeasure, ae_add_measure_iff]
  constructor
  · rw [ae_dirac_iff measurableSet_thetaCuspReciprocalGapSupport]
    exact reciprocalGap_mem_zero_oneThird_of_zero_or_three_le (Or.inl rfl)
  · filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)] with r hr
    exact reciprocalGap_mem_zero_oneThird_of_zero_or_three_le (Or.inr hr)

/-- The explicit reciprocal-likelihood candidate is finite. -/
theorem thetaCuspCassiniReciprocalLikelihoodMeasure_finite :
    IsFiniteMeasure thetaCuspCassiniReciprocalLikelihoodMeasure := by
  have hB : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos le_rfl
  letI : IsFiniteMeasure (thetaCuspLikelihoodSeamTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspLikelihoodSeamTiltedMeasure_finite hB
  rw [thetaCuspCassiniReciprocalLikelihoodMeasure]
  infer_instance

/-- Reciprocal square gaps give the strict compact support bound `[0, 1/3]`, stronger than the
`B < 1/2` required by analytic transport. -/
theorem ae_thetaCuspCassiniReciprocalLikelihoodMeasure_support :
    ∀ᵐ x ∂thetaCuspCassiniReciprocalLikelihoodMeasure,
      0 ≤ x ∧ |x| ≤ 1 / 3 := by
  rw [thetaCuspCassiniReciprocalLikelihoodMeasure,
    ae_map_iff measurable_thetaCuspLikelihoodReciprocalGap.aemeasurable
      measurableSet_thetaCuspReciprocalSupport]
  exact ae_reciprocalGap_mem_zero_oneThird_seamTilted

/-- Higher-tail mass is strictly positive: exponential tilt preserves the first square-gap atom
at `3`. -/
theorem thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos :
    0 < thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0) Set.univ := by
  have hthree : thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0) {3} ≠ 0 := by
    have h := thetaCuspLikelihoodSeamTiltedMeasure_singleton_three_ne_zero
      (thetaCuspLikelihoodCoordinate 0)
    rw [thetaCuspLikelihoodSeamTiltedMeasure, Measure.add_apply] at h
    simpa using h
  apply bot_lt_iff_ne_bot.mpr
  intro hzero
  have hle : thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0) {3} ≤
      thetaCuspHigherLikelihoodTiltedMeasure
        (thetaCuspLikelihoodCoordinate 0) Set.univ :=
    measure_mono (Set.subset_univ {3})
  rw [hzero] at hle
  exact hthree (bot_unique hle)

/-- The unit seam atom and positive higher-tail mass force the reciprocal pushforward to have
total `ENNReal` mass strictly larger than one. -/
theorem thetaCuspCassiniReciprocalLikelihoodMeasure_univ_gt_one :
    1 < thetaCuspCassiniReciprocalLikelihoodMeasure Set.univ := by
  rw [thetaCuspCassiniReciprocalLikelihoodMeasure,
    Measure.map_apply measurable_thetaCuspLikelihoodReciprocalGap MeasurableSet.univ]
  simp only [preimage_univ]
  rw [thetaCuspLikelihoodSeamTiltedMeasure, Measure.add_apply]
  have hdirac : Measure.dirac (0 : ℝ) Set.univ = 1 := by simp
  rw [hdirac]
  exact ENNReal.lt_add_right (by norm_num)
    thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos.ne'

/-- Finite-mass real form of the same normalization obstruction. -/
theorem thetaCuspCassiniReciprocalLikelihoodMeasure_measureReal_univ_gt_one :
    1 < thetaCuspCassiniReciprocalLikelihoodMeasure.real Set.univ := by
  letI : IsFiniteMeasure thetaCuspCassiniReciprocalLikelihoodMeasure :=
    thetaCuspCassiniReciprocalLikelihoodMeasure_finite
  rw [Measure.real_def]
  exact (ENNReal.toReal_lt_toReal (by norm_num)
    (measure_ne_top thetaCuspCassiniReciprocalLikelihoodMeasure Set.univ)).2
      thetaCuspCassiniReciprocalLikelihoodMeasure_univ_gt_one

/-- Rejected identity for the raw reciprocal-gap pushforward. It is retained as a named interface
so the exact normalization obstruction can be stated and downstream vacuous uses can be detected. -/
def ThetaCuspCassiniReciprocalLikelihoodBoundaryIdentity : Prop :=
  (fun u : ℝ => compactMarkovTransform
      thetaCuspCassiniReciprocalLikelihoodMeasure ((u : ℂ) - 1)) =ᶠ[
    nhdsWithin 0 (Ioi 0)] thetaCuspCassiniInwardCoordinateResponse

/-- Finiteness and support are unconditional; only the explicit transform identity remains. -/
theorem thetaCuspCassiniCompactMarkovBoundaryRepresentation_of_reciprocalLikelihoodIdentity
    (h : ThetaCuspCassiniReciprocalLikelihoodBoundaryIdentity) :
    ThetaCuspCassiniCompactMarkovBoundaryRepresentation := by
  refine ⟨thetaCuspCassiniReciprocalLikelihoodMeasure, 1 / 3,
    thetaCuspCassiniReciprocalLikelihoodMeasure_finite, by norm_num, by norm_num,
    ae_thetaCuspCassiniReciprocalLikelihoodMeasure_support, h⟩

/-- Logical endpoint retained for compatibility; the premise is disproved below. -/
theorem riemannHypothesis_of_thetaCuspCassiniReciprocalLikelihoodBoundaryIdentity
    (h : ThetaCuspCassiniReciprocalLikelihoodBoundaryIdentity) :
    RiemannHypothesis :=
  riemannHypothesis_of_thetaCuspCassiniCompactMarkovBoundaryRepresentation
    (thetaCuspCassiniCompactMarkovBoundaryRepresentation_of_reciprocalLikelihoodIdentity h)

/-- **Raw reciprocal-gap no-go.** The explicit seam carrier cannot represent the Cassini boundary:
analytic transport would force its total mass to be `normalizedPrimeArchMoment 0 < 1`, while its
unit origin atom plus the positive square-gap tail give mass strictly larger than one. -/
theorem not_thetaCuspCassiniReciprocalLikelihoodBoundaryIdentity :
    ¬ ThetaCuspCassiniReciprocalLikelihoodBoundaryIdentity := by
  intro hidentity
  have hgerm : completedSeamMomentGerm =ᶠ[nhds 0]
      compactMarkovTransform thetaCuspCassiniReciprocalLikelihoodMeasure :=
    completedSeamMomentGerm_eventuallyEq_compactMarkovTransform_of_thetaBoundary
      thetaCuspCassiniReciprocalLikelihoodMeasure_finite (by norm_num) (by norm_num)
      ae_thetaCuspCassiniReciprocalLikelihoodMeasure_support hidentity
  have hmass :=
    normalizedPrimeArchMoment_zero_eq_measureReal_univ_of_compactMarkovGerm
      thetaCuspCassiniReciprocalLikelihoodMeasure hgerm
  have hsource := normalizedPrimeArchMoment_zero_lt_one
  have hcand :=
    thetaCuspCassiniReciprocalLikelihoodMeasure_measureReal_univ_gt_one
  rw [hmass] at hsource
  linarith

/-! ## Positive survivor: source-normalized higher-tail reciprocal carrier -/

/-- Genuine higher square-gap carrier pushed through reciprocal gaps, without the artificial unit
atom at the seam origin. -/
def thetaCuspCassiniHigherReciprocalLikelihoodMeasure : Measure ℝ :=
  Measure.map thetaCuspLikelihoodReciprocalGap
    (thetaCuspHigherLikelihoodTiltedMeasure (thetaCuspLikelihoodCoordinate 0))

theorem thetaCuspCassiniHigherReciprocalLikelihoodMeasure_finite :
    IsFiniteMeasure thetaCuspCassiniHigherReciprocalLikelihoodMeasure := by
  have hB : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos le_rfl
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspHigherLikelihoodTiltedMeasure_finite hB
  rw [thetaCuspCassiniHigherReciprocalLikelihoodMeasure]
  infer_instance

theorem ae_thetaCuspCassiniHigherReciprocalLikelihoodMeasure_support :
    ∀ᵐ x ∂thetaCuspCassiniHigherReciprocalLikelihoodMeasure,
      0 ≤ x ∧ |x| ≤ 1 / 3 := by
  rw [thetaCuspCassiniHigherReciprocalLikelihoodMeasure,
    ae_map_iff measurable_thetaCuspLikelihoodReciprocalGap.aemeasurable
      measurableSet_thetaCuspReciprocalSupport]
  filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)] with r hr
  exact reciprocalGap_mem_zero_oneThird_of_zero_or_three_le (Or.inr hr)

theorem thetaCuspCassiniHigherReciprocalLikelihoodMeasure_univ_pos :
    0 < thetaCuspCassiniHigherReciprocalLikelihoodMeasure Set.univ := by
  rw [thetaCuspCassiniHigherReciprocalLikelihoodMeasure,
    Measure.map_apply measurable_thetaCuspLikelihoodReciprocalGap MeasurableSet.univ]
  simpa only [preimage_univ] using
    thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos

/-- Unique scalar that calibrates the genuine higher-tail reciprocal carrier to the canonical
zeroth source moment. -/
def thetaCuspCassiniHigherReciprocalCalibration : ENNReal :=
  ENNReal.ofReal (normalizedPrimeArchMoment 0) /
    thetaCuspCassiniHigherReciprocalLikelihoodMeasure Set.univ

/-- Corrected source-built candidate after deleting the obstructing origin atom and fixing its
only possible total-mass normalization. -/
def thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure : Measure ℝ :=
  thetaCuspCassiniHigherReciprocalCalibration •
    thetaCuspCassiniHigherReciprocalLikelihoodMeasure

/-- Calibration discharges the zeroth moment exactly in `ENNReal`. -/
theorem thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_univ :
    thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure Set.univ =
      ENNReal.ofReal (normalizedPrimeArchMoment 0) := by
  rw [thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure,
    Measure.smul_apply, smul_eq_mul, thetaCuspCassiniHigherReciprocalCalibration]
  exact ENNReal.div_mul_cancel
    thetaCuspCassiniHigherReciprocalLikelihoodMeasure_univ_pos.ne'
    (by
      letI : IsFiniteMeasure thetaCuspCassiniHigherReciprocalLikelihoodMeasure :=
        thetaCuspCassiniHigherReciprocalLikelihoodMeasure_finite
      exact measure_ne_top thetaCuspCassiniHigherReciprocalLikelihoodMeasure Set.univ)

theorem thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_finite :
    IsFiniteMeasure thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure := by
  refine IsFiniteMeasure.mk ?_
  rw [thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_univ]
  exact ENNReal.ofReal_lt_top

theorem ae_thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_support :
    ∀ᵐ x ∂thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure,
      0 ≤ x ∧ |x| ≤ 1 / 3 := by
  rw [thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure]
  exact Measure.ae_smul_measure
    ae_thetaCuspCassiniHigherReciprocalLikelihoodMeasure_support _

/-- Real zeroth-moment identity used by the moment capstone. -/
theorem thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_measureReal_univ :
    thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure.real Set.univ =
      normalizedPrimeArchMoment 0 := by
  rw [Measure.real_def,
    thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_univ,
    ENNReal.toReal_ofReal normalizedPrimeArchMoment_zero_pos.le]

/-- Remaining corrected interface begins at positive degree; finiteness, positivity, compact
support, and degree zero are already unconditional. -/
def ThetaCuspCassiniCalibratedReciprocalPositiveMomentMatching : Prop :=
  ∀ k : ℕ, 0 < k →
    normalizedPrimeArchMoment k =
      ∫ x : ℝ, x ^ k ∂thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure

/-- Positive-degree matching for the corrected source carrier extends to the complete moment
representation because degree zero was fixed by calibration. -/
theorem primeArchMomentRepresentation_of_thetaCuspCassiniCalibratedReciprocalPositiveMomentMatching
    (hmatch : ThetaCuspCassiniCalibratedReciprocalPositiveMomentMatching) :
    PrimeArchMomentRepresentation := by
  let μ := thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure
  letI : IsFiniteMeasure μ :=
    thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_finite
  have hsupport : ∀ᵐ x : ℝ ∂μ, 0 ≤ x ∧ |x| ≤ 1 / 3 :=
    ae_thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_support
  refine ⟨μ, ?_, ?_⟩
  · intro k
    cases k with
    | zero =>
        simp only [pow_zero]
        rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
        exact thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure_measureReal_univ.symm
    | succ k =>
        exact hmatch (k + 1) (by omega)
  · intro k
    have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ k) μ :=
      (continuous_id.pow k).aestronglyMeasurable
    refine Integrable.of_bound hmeas ((1 / 3 : ℝ) ^ k) ?_
    filter_upwards [hsupport] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx.2 k

/-- Corrected right-to-left endpoint: only positive-degree moment identification remains. -/
theorem riemannHypothesis_of_thetaCuspCassiniCalibratedReciprocalPositiveMomentMatching
    (hmatch : ThetaCuspCassiniCalibratedReciprocalPositiveMomentMatching) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchMomentRepresentation
    (primeArchMomentRepresentation_of_thetaCuspCassiniCalibratedReciprocalPositiveMomentMatching
      hmatch)

end

end RHTower
