import GaloisForLFunctions.HTGeometry.AnalyticCircleMean
import GaloisForLFunctions.HTGeometry.BoundedPhaseSmirnovToeplitz
import GaloisForLFunctions.HTGeometry.DiskSmirnovAnalyticValue
import GaloisForLFunctions.HTGeometry.SzegoLowerBoundGeneral
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryInnerOuterFactor

/-!
# Bounded-phase half-power Smirnov Toeplitz elements

A bounded measurable real phase has a Herglotz analytic lift.  Its reciprocal sector exponential
has uniformly bounded half-power circle means.  Radial Fatou gives exact circle-boundary
integrability, and the fourth-order Cayley decay `(1-z)^4` transports that admission to Lebesgue
measure on the real line.  The resulting nonzero Toeplitz-kernel element is unconditional.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_exp_half_le_two_re_of_abs_re_le {w : ℂ} (hw : |w.re| ≤ Real.pi / 2) :
    ‖Complex.exp (-I * w / 2)‖ ≤
      2 * (Complex.exp (-I * w / 2)).re := by
  have him : |(-I * w / 2).im| ≤ Real.pi / 4 := by
    have heq : (-I * w / 2).im = -w.re / 2 := by
      norm_num [Complex.div_im, Complex.mul_im, Complex.normSq]
    rw [heq, abs_div]
    norm_num
    linarith
  have hcos : 1 / 2 ≤ Real.cos (-I * w / 2).im := by
    rw [← Real.cos_pi_div_three]
    calc
      Real.cos (Real.pi / 3) ≤ Real.cos |(-I * w / 2).im| := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        · exact abs_nonneg _
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      _ = Real.cos (-I * w / 2).im := Real.cos_abs _
  rw [Complex.norm_exp, Complex.exp_re]
  nlinarith [Real.exp_pos (-I * w / 2).re]

theorem sqrt_norm_sectorCayley_reciprocal {w : ℂ}
    (hw : |w.re| ≤ Real.pi / 2) :
    Real.sqrt ‖(1 - sectorCayleyValue w) / (1 + sectorCayleyValue w)‖ =
      ‖Complex.exp (-I * w / 2)‖ := by
  have he : sectorExponential w ≠ 0 := sectorExponential_ne_zero w
  have hden : sectorExponential w + 1 ≠ 0 :=
    add_one_ne_zero_of_re_nonneg (sectorExponential_re_nonneg hw)
  have hquot : (1 - sectorCayleyValue w) / (1 + sectorCayleyValue w) =
      (sectorExponential w)⁻¹ := by
    unfold sectorCayleyValue
    field_simp [hden, he]
    ring
  rw [hquot, sectorExponential, norm_inv, Complex.norm_exp, Complex.norm_exp]
  have hre : -(I * w).re = 2 * (-I * w / 2).re := by
    norm_num [Complex.div_re, Complex.mul_re, Complex.normSq]
    ring
  rw [← Real.exp_neg, hre,
    show 2 * (-I * w / 2).re =
      (-I * w / 2).re + (-I * w / 2).re by ring,
    Real.exp_add, ← pow_two, Real.sqrt_sq_eq_abs,
    abs_of_pos (Real.exp_pos _)]

def boundedPhaseReciprocal (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) : DiskSmirnovBoundary where
  numerator := boundedPhaseMinus b hb hbound
  denominator := boundedPhasePlus b hb hbound
  denominator_outer := isOuterDiskMultiplier_boundedPhasePlus b hb hbound

def boundedPhaseHalfValue (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) (z : ℂ) : ℂ :=
  Complex.exp (-I * hardyFun (boundedPhaseHardy b hb hbound) z / 2)

theorem boundedPhaseReciprocal_radial_sqrt_eq
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) (n : ℕ) (z : Circle) :
    Real.sqrt ‖(boundedPhaseReciprocal b hb hbound).radialBoundaryFun n z‖ =
      ‖boundedPhaseHalfValue b hb hbound
        ((hardyDiskAbelRadius n : ℂ) * (z : ℂ))‖ := by
  let w := hardyFun (boundedPhaseHardy b hb hbound)
    ((hardyDiskAbelRadius n : ℂ) * (z : ℂ))
  have hz : ‖(hardyDiskAbelRadius n : ℂ) * (z : ℂ)‖ < 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hardyDiskAbelRadius_nonneg n), Circle.norm_coe, mul_one]
    exact hardyDiskAbelRadius_lt_one n
  have hw : |w.re| ≤ Real.pi / 2 :=
    boundedPhaseHardy_re_bound b hb hbound _ hz
  change Real.sqrt ‖(1 - sectorCayleyValue w) / (1 + sectorCayleyValue w)‖ =
    ‖Complex.exp (-I * w / 2)‖
  exact sqrt_norm_sectorCayley_reciprocal hw

theorem analyticOnNhd_boundedPhaseHalfValue
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    AnalyticOnNhd ℂ (boundedPhaseHalfValue b hb hbound) (Metric.ball 0 1) := by
  intro z hz
  have hH : AnalyticAt ℂ
      (hardyFun (boundedPhaseHardy b hb hbound)) z :=
    (differentiableOn_hardyFun (boundedPhaseHardy b hb hbound)).analyticOnNhd
      Metric.isOpen_ball z hz
  change AnalyticAt ℂ
    (fun w => Complex.exp (-I * hardyFun (boundedPhaseHardy b hb hbound) w / 2)) z
  fun_prop

theorem intervalIntegral_norm_boundedPhaseHalfValue_le
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖boundedPhaseHalfValue b hb hbound (circleMap 0 r θ)‖) ≤
      2 * (((2 * Real.pi : ℂ) * boundedPhaseHalfValue b hb hbound 0).re) := by
  let q := boundedPhaseHalfValue b hb hbound
  have hqAna : AnalyticOnNhd ℂ q (Metric.ball 0 1) :=
    analyticOnNhd_boundedPhaseHalfValue b hb hbound
  have harg : ∀ θ : ℝ, circleMap 0 r θ ∈ Metric.ball (0 : ℂ) 1 := by
    intro θ
    rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg hr0]
    exact hr1
  have hqCont : Continuous (fun θ : ℝ => q (circleMap 0 r θ)) :=
    hqAna.continuousOn.comp_continuous (continuous_circleMap 0 r) harg
  have hnormII : IntervalIntegrable
      (fun θ : ℝ => ‖q (circleMap 0 r θ)‖) volume 0 (2 * Real.pi) :=
    hqCont.norm.intervalIntegrable _ _
  have hreII : IntervalIntegrable
      (fun θ : ℝ => 2 * (q (circleMap 0 r θ)).re) volume 0 (2 * Real.pi) :=
    (continuous_const.mul (Complex.continuous_re.comp hqCont)).intervalIntegrable _ _
  have hqIoc : Integrable (fun θ : ℝ => q (circleMap 0 r θ))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    change IntegrableOn (fun θ : ℝ => q (circleMap 0 r θ))
      (Set.Ioc 0 (2 * Real.pi)) volume
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp
      (hqCont.intervalIntegrable _ _)
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖q (circleMap 0 r θ)‖) ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          2 * (q (circleMap 0 r θ)).re := by
      apply intervalIntegral.integral_mono_on (by positivity) hnormII hreII
      intro θ hθ
      apply norm_exp_half_le_two_re_of_abs_re_le
      exact boundedPhaseHardy_re_bound b hb hbound _ (by
        simpa [Metric.mem_ball, dist_zero_right] using harg θ)
    _ = 2 * ((∫ θ in (0 : ℝ)..(2 * Real.pi),
        q (circleMap 0 r θ))).re := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_of_le (by positivity),
        intervalIntegral.integral_of_le (by positivity)]
      exact integral_re hqIoc
    _ = 2 * (((2 * Real.pi : ℂ) * q 0).re) := by
      rw [integral_circleMap_eq_center_of_analyticOnNhd_unitBall hqAna hr0 hr1]

theorem circleIntegral_boundedPhaseReciprocal_radial_sqrt_le
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) (n : ℕ) :
    (∫ z : Circle,
        Real.sqrt ‖(boundedPhaseReciprocal b hb hbound).radialBoundaryFun n z‖
          ∂circleLebesgue) ≤
      (2 * Real.pi)⁻¹ *
        (2 * (((2 * Real.pi : ℂ) * boundedPhaseHalfValue b hb hbound 0).re)) := by
  let q := boundedPhaseHalfValue b hb hbound
  let r : ℝ := hardyDiskAbelRadius n
  have hqAna : AnalyticOnNhd ℂ q (Metric.ball 0 1) :=
    analyticOnNhd_boundedPhaseHalfValue b hb hbound
  have harg : ∀ z : Circle, (r : ℂ) * (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    intro z
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hardyDiskAbelRadius_nonneg n), Circle.norm_coe, mul_one]
    exact hardyDiskAbelRadius_lt_one n
  have hcont : Continuous (fun z : Circle => ‖q ((r : ℂ) * (z : ℂ))‖) :=
    (hqAna.continuousOn.comp_continuous
      (continuous_const.mul continuous_subtype_val) harg).norm
  calc
    (∫ z : Circle,
        Real.sqrt ‖(boundedPhaseReciprocal b hb hbound).radialBoundaryFun n z‖
          ∂circleLebesgue) =
        ∫ z : Circle, ‖q ((r : ℂ) * (z : ℂ))‖ ∂circleLebesgue := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => boundedPhaseReciprocal_radial_sqrt_eq b hb hbound n z
    _ = Real.circleAverage (fun w : ℂ => ‖q ((r : ℂ) * w)‖) 0 1 := by
      exact integral_circleLebesgue_eq_circleAverage
        (fun w : ℂ => ‖q ((r : ℂ) * w)‖) hcont.aestronglyMeasurable
    _ = (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖q (circleMap 0 r θ)‖) := by
      rw [Real.circleAverage]
      congr 2
      funext θ
      congr 2
      simp [circleMap]
    _ ≤ (2 * Real.pi)⁻¹ *
        (2 * (((2 * Real.pi : ℂ) * q 0).re)) := by
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral_norm_boundedPhaseHalfValue_le b hb hbound
          (hardyDiskAbelRadius_nonneg n) (hardyDiskAbelRadius_lt_one n))
        (by positivity)

theorem integrable_circleBoundary_sqrt_boundedPhaseReciprocal
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    Integrable (fun z : Circle =>
      Real.sqrt ‖(boundedPhaseReciprocal b hb hbound).circleBoundary z‖)
      circleLebesgue := by
  let F := boundedPhaseReciprocal b hb hbound
  let q := boundedPhaseHalfValue b hb hbound
  let C : ℝ := (2 * Real.pi)⁻¹ *
    (2 * (((2 * Real.pi : ℂ) * q 0).re))
  obtain ⟨ns, hns, hconv⟩ := F.exists_radialBoundary_subseq_ae
  let g : ℕ → Circle → ℝ≥0∞ := fun i z =>
    ENNReal.ofReal ‖q ((hardyDiskAbelRadius (ns i) : ℂ) * (z : ℂ))‖
  have hgMeas : ∀ i, Measurable (g i) := by
    intro i
    have harg : ∀ z : Circle,
        (hardyDiskAbelRadius (ns i) : ℂ) * (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      intro z
      rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg (ns i)), Circle.norm_coe, mul_one]
      exact hardyDiskAbelRadius_lt_one (ns i)
    have hc : Continuous (fun z : Circle =>
        ‖q ((hardyDiskAbelRadius (ns i) : ℂ) * (z : ℂ))‖) :=
      ((analyticOnNhd_boundedPhaseHalfValue b hb hbound).continuousOn.comp_continuous
        (continuous_const.mul continuous_subtype_val) harg).norm
    exact (ENNReal.continuous_ofReal.comp hc).measurable
  have hgBound : ∀ i, (∫⁻ z : Circle, g i z ∂circleLebesgue) ≤ ENNReal.ofReal C := by
    intro i
    have harg : ∀ z : Circle,
        (hardyDiskAbelRadius (ns i) : ℂ) * (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      intro z
      rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg (ns i)), Circle.norm_coe, mul_one]
      exact hardyDiskAbelRadius_lt_one (ns i)
    have hc : Continuous (fun z : Circle =>
        ‖q ((hardyDiskAbelRadius (ns i) : ℂ) * (z : ℂ))‖) :=
      ((analyticOnNhd_boundedPhaseHalfValue b hb hbound).continuousOn.comp_continuous
        (continuous_const.mul continuous_subtype_val) harg).norm
    have hi : Integrable (fun z : Circle =>
        ‖q ((hardyDiskAbelRadius (ns i) : ℂ) * (z : ℂ))‖)
        circleLebesgue := by
      simpa using
        hc.continuousOn.integrableOn_compact (K := Set.univ)
          (μ := circleLebesgue) isCompact_univ
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun _ => norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (∫ z : Circle,
          ‖q ((hardyDiskAbelRadius (ns i) : ℂ) * (z : ℂ))‖
            ∂circleLebesgue) =
          ∫ z : Circle,
            Real.sqrt ‖F.radialBoundaryFun (ns i) z‖ ∂circleLebesgue := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => (boundedPhaseReciprocal_radial_sqrt_eq b hb hbound (ns i) z).symm
      _ ≤ C := circleIntegral_boundedPhaseReciprocal_radial_sqrt_le b hb hbound (ns i)
  have hfatou := lintegral_liminf_le (μ := circleLebesgue) hgMeas
      (u := atTop)
  have hliminfBound : liminf (fun i => ∫⁻ z : Circle, g i z ∂circleLebesgue) atTop ≤
      ENNReal.ofReal C := by
    exact liminf_le_of_frequently_le (Eventually.of_forall hgBound).frequently
  have hpoint : ∀ᵐ z ∂circleLebesgue,
      liminf (fun i => g i z) atTop =
        ENNReal.ofReal (Real.sqrt ‖F.circleBoundary z‖) := by
    filter_upwards [hconv] with z hz
    have ht : Tendsto (fun i =>
        Real.sqrt ‖F.radialBoundaryFun (ns i) z‖) atTop
        (nhds (Real.sqrt ‖F.circleBoundary z‖)) := hz.norm.sqrt
    have ht' : Tendsto (fun i =>
        ‖q ((hardyDiskAbelRadius (ns i) : ℂ) * (z : ℂ))‖) atTop
        (nhds (Real.sqrt ‖F.circleBoundary z‖)) := by
      apply ht.congr'
      exact Eventually.of_forall fun i => boundedPhaseReciprocal_radial_sqrt_eq b hb hbound (ns i) z
    exact (ENNReal.tendsto_ofReal ht').liminf_eq
  have hfinite : (∫⁻ z : Circle,
      ENNReal.ofReal (Real.sqrt ‖F.circleBoundary z‖) ∂circleLebesgue) < ∞ := by
    calc
      (∫⁻ z : Circle,
          ENNReal.ofReal (Real.sqrt ‖F.circleBoundary z‖) ∂circleLebesgue) =
          ∫⁻ z : Circle, liminf (fun i => g i z) atTop ∂circleLebesgue := by
        apply lintegral_congr_ae
        filter_upwards [hpoint] with z hz
        exact hz.symm
      _ ≤ liminf (fun i => ∫⁻ z : Circle, g i z ∂circleLebesgue) atTop := hfatou
      _ ≤ ENNReal.ofReal C := hliminfBound
      _ < ∞ := ENNReal.ofReal_lt_top
  have hnum := diskMultiplierBoundaryMeasurableRep_ae F.numerator
  have hden := diskMultiplierBoundaryMeasurableRep_ae F.denominator
  have hrep : (fun z : Circle => Real.sqrt ‖F.circleBoundary z‖) =ᵐ[circleLebesgue]
      fun z => Real.sqrt ‖F.circleBoundaryMeasurableRep z‖ := by
    filter_upwards [hnum, hden] with z hzNum hzDen
    simp only [DiskSmirnovBoundary.circleBoundary,
      DiskSmirnovBoundary.circleBoundaryMeasurableRep, hzNum, hzDen]
  refine ⟨(measurable_norm.comp F.measurable_circleBoundaryMeasurableRep).sqrt.aestronglyMeasurable.congr
      hrep.symm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun z => Real.sqrt_nonneg _)]
  exact hfinite

theorem diskMultiplierLineBoundary_diskMonomialMultiplier_one_ae :
    diskMultiplierLineBoundary (diskMonomialMultiplier 1) =ᵐ[volume]
      fun x => realCayley x := by
  have hcircle : diskMultiplierBoundaryFun (diskMonomialMultiplier 1) =ᵐ[
      circleLebesgue] fun z => (z : ℂ) := by
    rw [diskMultiplierBoundaryFun, hardyOf_diskMonomialMultiplier,
      hardyDiskBoundary_single]
    filter_upwards [circleMonomialLp_coeFn_ae circleLebesgue 1] with z hz
    simpa using hz
  have hweighted := hcircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hline : (fun x => diskMultiplierBoundaryFun (diskMonomialMultiplier 1)
      (circleCayley x)) =ᵐ[volume] fun x => (circleCayley x : ℂ) :=
    (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mp hweighted
  filter_upwards [diskMultiplierLineBoundary_ae (diskMonomialMultiplier 1), hline]
      with x hxRep hxValue
  rw [hxRep, hxValue, circleCayley_coe]

def oneSubDiskMultiplier : DiskMultiplier :=
  (DiskMultiplier.const 1).sub (diskMonomialMultiplier 1)

def oneSubDiskMultiplierFourth : DiskMultiplier :=
  let A := oneSubDiskMultiplier
  (A.mul A).mul (A.mul A)

theorem diskMultiplierLineBoundary_oneSubDiskMultiplierFourth_ae :
    diskMultiplierLineBoundary oneSubDiskMultiplierFourth =ᵐ[volume]
      fun x => (1 - realCayley x) ^ 4 := by
  have hOne := diskMultiplierLineBoundary_const_ae (1 : ℂ)
  have hZ := diskMultiplierLineBoundary_diskMonomialMultiplier_one_ae
  have hA := diskMultiplierLineBoundary_sub_ae
    (DiskMultiplier.const 1) (diskMonomialMultiplier 1)
  have hAA := diskMultiplierLineBoundary_mul_ae oneSubDiskMultiplier oneSubDiskMultiplier
  have hFourth := diskMultiplierLineBoundary_mul_ae
    (oneSubDiskMultiplier.mul oneSubDiskMultiplier) (oneSubDiskMultiplier.mul oneSubDiskMultiplier)
  filter_upwards [hOne, hZ, hA, hAA, hFourth]
      with x hxOne hxZ hxA hxAA hxFourth
  change diskMultiplierLineBoundary
      ((oneSubDiskMultiplier.mul oneSubDiskMultiplier).mul
        (oneSubDiskMultiplier.mul oneSubDiskMultiplier)) x = _
  rw [hxFourth, hxAA]
  have hxA' : diskMultiplierLineBoundary oneSubDiskMultiplier x = 1 - realCayley x := by
    simpa [oneSubDiskMultiplier, hxOne, hxZ] using hxA
  rw [hxA']
  ring

theorem norm_one_sub_realCayley_sq (x : ℝ) :
    ‖1 - realCayley x‖ ^ 2 = 4 * Real.pi * standardCauchyWeight x := by
  rw [standardCauchyWeight, realCayley]
  have hden : (x : ℂ) + I ≠ 0 := real_add_I_ne_zero x
  rw [show (1 : ℂ) - ((x : ℂ) - I) / ((x : ℂ) + I) =
      2 * I / ((x : ℂ) + I) by field_simp; ring]
  rw [norm_div, norm_mul, norm_ofNat, norm_I, mul_one, div_pow]
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num
  field_simp
  ring

theorem DiskSmirnovBoundary.boundary_eq_circleBoundary_cayley_ae (F : DiskSmirnovBoundary) :
    F.boundary =ᵐ[volume] fun x => F.circleBoundary (circleCayley x) := by
  filter_upwards [diskMultiplierLineBoundary_ae F.numerator,
      diskMultiplierLineBoundary_ae F.denominator] with x hxNum hxDen
  simp only [DiskSmirnovBoundary.boundary, DiskSmirnovBoundary.circleBoundary,
    hxNum, hxDen]

def boundedPhaseHalfForward (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) : DiskSmirnovBoundary where
  numerator := oneSubDiskMultiplierFourth.mul (boundedPhaseMinus b hb hbound)
  denominator := boundedPhasePlus b hb hbound
  denominator_outer := isOuterDiskMultiplier_boundedPhasePlus b hb hbound

theorem integrable_sqrt_boundary_boundedPhaseHalfForward
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    Integrable (fun x : ℝ =>
      Real.sqrt ‖(boundedPhaseHalfForward b hb hbound).boundary x‖) := by
  let R := boundedPhaseReciprocal b hb hbound
  let F := boundedPhaseHalfForward b hb hbound
  let hCircle : Circle → ℝ := fun z => Real.sqrt ‖R.circleBoundary z‖
  have hCircleInt : Integrable hCircle circleLebesgue :=
    integrable_circleBoundary_sqrt_boundedPhaseReciprocal b hb hbound
  have hWeighted : Integrable (hCircle ∘ circleCayley)
      ((volume : Measure ℝ).withDensity (realDensity standardCauchyWeight)) :=
    (circleCayley_weighted_measurePreserving.integrable_comp
      hCircleInt.aestronglyMeasurable).2 hCircleInt
  have hWeightedLeb : Integrable (fun x : ℝ =>
      hCircle (circleCayley x) * standardCauchyWeight x) volume := by
    have hw := (integrable_withDensity_iff
      (measurable_realDensity measurable_standardCauchyWeight)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hWeighted
    simpa only [Function.comp_apply, realDensity, ENNReal.toReal_ofReal,
      (standardCauchyWeight_pos _).le] using hw
  have hMajorant : Integrable (fun x : ℝ =>
      (4 * Real.pi) * (hCircle (circleCayley x) * standardCauchyWeight x)) volume :=
    hWeightedLeb.const_mul (4 * Real.pi)
  have hMul := diskMultiplierLineBoundary_mul_ae
    oneSubDiskMultiplierFourth (boundedPhaseMinus b hb hbound)
  have hA := diskMultiplierLineBoundary_oneSubDiskMultiplierFourth_ae
  have hR := DiskSmirnovBoundary.boundary_eq_circleBoundary_cayley_ae R
  have heq : (fun x : ℝ => Real.sqrt ‖F.boundary x‖) =ᵐ[volume]
      fun x => (4 * Real.pi) *
        (hCircle (circleCayley x) * standardCauchyWeight x) := by
    filter_upwards [hMul, hA, hR] with x hxMul hxA hxR
    change Real.sqrt ‖diskMultiplierLineBoundary
        (oneSubDiskMultiplierFourth.mul (boundedPhaseMinus b hb hbound)) x /
          diskMultiplierLineBoundary (boundedPhasePlus b hb hbound) x‖ = _
    rw [hxMul]
    have hfactor : diskMultiplierLineBoundary oneSubDiskMultiplierFourth x *
        diskMultiplierLineBoundary (boundedPhaseMinus b hb hbound) x /
          diskMultiplierLineBoundary (boundedPhasePlus b hb hbound) x =
        diskMultiplierLineBoundary oneSubDiskMultiplierFourth x * R.boundary x := by
      change _ = diskMultiplierLineBoundary oneSubDiskMultiplierFourth x *
        (diskMultiplierLineBoundary (boundedPhaseMinus b hb hbound) x /
          diskMultiplierLineBoundary (boundedPhasePlus b hb hbound) x)
      ring
    rw [hfactor, norm_mul, Real.sqrt_mul (norm_nonneg _), hxA,
      norm_pow]
    have hsqrt : Real.sqrt (‖1 - realCayley x‖ ^ 4) =
        ‖1 - realCayley x‖ ^ 2 := by
      rw [show ‖1 - realCayley x‖ ^ 4 =
          (‖1 - realCayley x‖ ^ 2) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hsqrt, norm_one_sub_realCayley_sq, hxR]
    ring
  exact hMajorant.congr heq.symm

/-- A nonzero Smirnov Toeplitz-kernel element whose forward boundary lies in the half-power
Hardy class on the line. -/
structure SmirnovToeplitzHalfKernelElement (U : ℝ → ℂ)
    extends SmirnovToeplitzKernelElement U where
  forward_half_integrable : Integrable (fun x : ℝ =>
    Real.sqrt ‖forward.boundary x‖)

/-- A half-power Toeplitz-kernel element depends only on the a.e. class of its symbol. -/
def SmirnovToeplitzHalfKernelElement.congr {U V : ℝ → ℂ}
    (F : SmirnovToeplitzHalfKernelElement U) (hUV : U =ᵐ[volume] V) :
    SmirnovToeplitzHalfKernelElement V where
  toSmirnovToeplitzKernelElement :=
    F.toSmirnovToeplitzKernelElement.congr hUV
  forward_half_integrable := F.forward_half_integrable

def boundedPhaseSmirnovToeplitzHalfElement
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    SmirnovToeplitzHalfKernelElement (boundedPhaseToeplitzSymbol b) where
  forward := boundedPhaseHalfForward b hb hbound
  reflected := boundedPhaseHalfForward b hb hbound
  boundary_relation := by
    let A := oneSubDiskMultiplierFourth
    let D := boundedPhaseMinus b hb hbound
    let P := boundedPhasePlus b hb hbound
    have hmul := diskMultiplierLineBoundary_mul_ae A D
    have hA := diskMultiplierLineBoundary_oneSubDiskMultiplierFourth_ae
    have hphase := boundedPhaseOuterQuotient_phase_ae b hb hbound
    have hPne := diskMultiplierLineBoundary_ne_zero_ae P
      (isOuterDiskMultiplier_boundedPhasePlus b hb hbound).exists_nonzero
    have hDne := diskMultiplierLineBoundary_ne_zero_ae D
      (isOuterDiskMultiplier_boundedPhaseMinus b hb hbound).exists_nonzero
    filter_upwards [hmul, hA, hphase, hPne, hDne]
        with x hxMul hxA hxPhase hxP hxD
    dsimp only at hxPhase
    change diskMultiplierLineBoundary (A.mul D) x /
        diskMultiplierLineBoundary P x =
      (starRingEnd ℂ) (boundedPhaseToeplitzSymbol b x) *
        (starRingEnd ℂ)
          (diskMultiplierLineBoundary (A.mul D) x /
            diskMultiplierLineBoundary P x)
    rw [hxMul, hxA, boundedPhaseToeplitzSymbol, ← hxPhase]
    let z : ℂ := realCayley x
    let a : ℂ := (1 - z) ^ 4
    have hzUnit : (starRingEnd ℂ) z * z = 1 := by
      rw [Complex.conj_mul', norm_realCayley]
      norm_num
    have hz : z ≠ 0 := by
      intro hzero
      rw [hzero] at hzUnit
      norm_num at hzUnit
    have hza : z ^ 4 * (starRingEnd ℂ) a = a := by
      have hzConj : z * (starRingEnd ℂ) z = 1 := by
        rw [mul_comm]
        exact hzUnit
      change z ^ 4 * (starRingEnd ℂ) ((1 - z) ^ 4) = (1 - z) ^ 4
      simp only [map_pow, map_sub, map_one]
      have hbase : z * (1 - (starRingEnd ℂ) z) = -(1 - z) := by
        calc
          z * (1 - (starRingEnd ℂ) z) = z - z * (starRingEnd ℂ) z := by ring
          _ = z - 1 := by rw [hzConj]
          _ = -(1 - z) := by ring
      rw [← mul_pow, hbase]
      ring
    have hcP : (starRingEnd ℂ) (diskMultiplierLineBoundary P x) ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 hxP
    have hcD : (starRingEnd ℂ) (diskMultiplierLineBoundary D x) ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 hxD
    change a * diskMultiplierLineBoundary D x /
        diskMultiplierLineBoundary P x =
      (starRingEnd ℂ)
          ((starRingEnd ℂ) (z ^ 4) *
            (diskMultiplierLineBoundary P x / diskMultiplierLineBoundary D x /
              (starRingEnd ℂ)
                (diskMultiplierLineBoundary P x / diskMultiplierLineBoundary D x))) *
        (starRingEnd ℂ)
          ((a * diskMultiplierLineBoundary D x) /
            diskMultiplierLineBoundary P x)
    simp only [map_mul, map_div₀, starRingEnd_self_apply, map_pow]
    field_simp [hz, hcP, hcD]
    rw [hza]
  forward_nonzero := by
    refine ⟨(1 / 2 : ℂ), ?_, ?_⟩
    · norm_num [Metric.mem_ball, dist_zero_right]
    · change oneSubDiskMultiplierFourth.fn (1 / 2 : ℂ) *
          (boundedPhaseMinus b hb hbound).fn (1 / 2 : ℂ) ≠ 0
      apply mul_ne_zero
      · norm_num [oneSubDiskMultiplierFourth, oneSubDiskMultiplier,
          diskMonomialMultiplier, DiskMultiplier.const, DiskMultiplier.sub,
          DiskMultiplier.mul]
      · intro hzero
        change 1 - sectorCayleyValue
          (hardyFun (boundedPhaseHardy b hb hbound) (1 / 2 : ℂ)) = 0 at hzero
        have hpos := one_sub_sectorCayleyValue_re_pos
          (boundedPhaseHardy_re_bound b hb hbound (1 / 2 : ℂ) (by norm_num))
        rw [hzero] at hpos
        norm_num at hpos
  forward_half_integrable := integrable_sqrt_boundary_boundedPhaseHalfForward b hb hbound

/-- Left multiplication by a nonzero bounded analytic multiplier preserves half-power admission. -/
def SmirnovToeplitzHalfKernelElement.mulLeftMultiplier
    {U : ℝ → ℂ} (G : SmirnovToeplitzHalfKernelElement U)
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    SmirnovToeplitzHalfKernelElement
      (smirnovToeplitzSymbolMul (diskMultiplierPhaseReflectionSymbol phi) U) := by
  let B := diskMultiplierSmirnovToeplitzElement phi hphi
  let K := B.mul G.toSmirnovToeplitzKernelElement
  refine
    { toSmirnovToeplitzKernelElement := K
      forward_half_integrable := ?_ }
  have hmul := B.forward.boundary_mul_ae G.forward
  have hphiBoundary := DiskSmirnovBoundary.boundary_ofMultiplier_ae phi
  have hbd := ae_norm_diskMultiplierLineBoundary_le phi
  have hscale : Integrable (fun x : ℝ =>
      Real.sqrt phi.bd * Real.sqrt ‖G.forward.boundary x‖) :=
    G.forward_half_integrable.const_mul (Real.sqrt phi.bd)
  apply hscale.mono'
  · exact (K.forward.measurable_boundary.norm.sqrt).aestronglyMeasurable
  · filter_upwards [hmul, hphiBoundary, hbd] with x hxMul hxPhi hxBd
    have hxPhi' : B.forward.boundary x = diskMultiplierLineBoundary phi x := by
      change (DiskSmirnovBoundary.ofMultiplier phi).boundary x = _
      exact hxPhi
    change ‖Real.sqrt ‖K.forward.boundary x‖‖ ≤
      Real.sqrt phi.bd * Real.sqrt ‖G.forward.boundary x‖
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    change Real.sqrt ‖(B.forward.mul G.forward).boundary x‖ ≤
      Real.sqrt phi.bd * Real.sqrt ‖G.forward.boundary x‖
    rw [hxMul, hxPhi', norm_mul,
      Real.sqrt_mul (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hxBd) (Real.sqrt_nonneg _)

end


end GaloisForLFunctions.HTGeometry
