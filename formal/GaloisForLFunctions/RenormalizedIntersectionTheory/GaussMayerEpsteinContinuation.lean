import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinIntegral
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinPeriod
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected

/-! The actual Epstein-to-Mayer Cauchy transform continues through the
source half-plane, including parameter one. Absolute convergence and
local domination identify the continued integral itself with the genuine
Mayer period, rather than continuing a divergent lattice sum. -/

open Complex Set Filter Metric Topology MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMellin
open MayerQuadraticCone MayerEpsteinQuadrants MayerEpsteinEndpointBounds MayerEpsteinIntegral
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinContinuation

private def sourceDomain : Set ℂ := {w : ℂ | 0 < w.re} \ {2}

private theorem sourceDomain_open : IsOpen sourceDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton

private theorem sourceDomain_preconnected : IsPreconnected sourceDomain := by
  have hc : Convex ℝ {w : ℂ | 0 < w.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq,Complex.add_re,Complex.smul_re,smul_eq_mul]
    by_cases ha0 : a=0
    · subst a
      have hb1 : b=1 := by simpa only [zero_add] using hab
      rw [hb1,zero_mul,zero_add,one_mul]
      exact hy
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hap hx) (mul_nonneg hb hy.le)
  exact GaloisForLFunctions.HTGeometry.isPreconnected_diff_of_countable_of_convex_complex hc
    (isOpen_lt continuous_const Complex.continuous_re) (countable_singleton 2)
    (a := (3 : ℂ)) (by norm_num)

private theorem differentiableAt_periodValue {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : a ∈ MayerScatteringPeriod.periodSegment) :
    DifferentiableAt ℂ (fun v => MayerScatteringPeriod.periodValue v a) w := by
  have hmem : (a : ℂ)-1 ∈ outer := by
    have he : ((a : ℂ)-1)-1=((a-2 : ℝ) : ℂ) := by push_cast; ring
    rw [outer,mem_closedBall,dist_eq_norm,he,Complex.norm_real,Real.norm_eq_abs,abs_le]
    constructor <;> linarith only [ha.1,ha.2]
  let z : Disc := ⟨(a : ℂ)-1,hmem⟩
  have he : (fun v => MayerScatteringPeriod.periodValue v a)=
      fun v => evaluation z (state v) := funext (fun v => plane_eq (state v) z)
  rw [he]
  exact (differentiableAt_const (evaluation z)).clm_apply (analyticAt_state hw hw2).differentiableAt

private def defect (a : ℝ) (w : ℂ) : ℂ :=
  MayerEpsteinIntegral.average w a-averagingFactor w*MayerScatteringPeriod.periodValue w a

private theorem analyticOn_defect {a : ℝ} (ha : a ∈ MayerScatteringPeriod.periodSegment) :
    AnalyticOnNhd ℂ (defect a) sourceDomain := by
  have ha0 : 0 < a := by linarith only [ha.1]
  have hd : DifferentiableOn ℂ (defect a) sourceDomain := by
    intro w hw
    have hw2 : w ≠ 2 := by simpa only [mem_singleton_iff] using hw.2
    exact ((differentiableAt_average hw.1 hw2 ha0).sub
      ((differentiableAt_averagingFactor hw.1).mul
        (differentiableAt_periodValue hw.1 hw2 ha))).differentiableWithinAt
  exact hd.analyticOnNhd sourceDomain_open

private theorem defect_absolute {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : a ∈ MayerScatteringPeriod.periodSegment) : defect a w=0 := by
  have ha0 : 0 < a := by linarith only [ha.1]
  rw [defect,MayerEpsteinIntegral.average,MayerEpsteinPeriod.epstein_average_eq hw ha0,
    MayerPeriodMellin.period_axes_decomposition hw ha,sub_self]

/-- The unnormalized integral identity holds throughout the punctured source half-plane. -/
theorem average_eq_period {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : a ∈ MayerScatteringPeriod.periodSegment) :
    MayerEpsteinIntegral.average w a=averagingFactor w*MayerScatteringPeriod.periodValue w a := by
  have he : defect a =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {v : ℂ | 2 < v.re} by norm_num)] with v hv
    exact defect_absolute hv ha
  have hz := (analyticOn_defect ha).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    sourceDomain_preconnected (show (3 : ℂ) ∈ sourceDomain by norm_num [sourceDomain]) he
    (show w ∈ sourceDomain from ⟨hw,by simpa only [mem_singleton_iff] using hw2⟩)
  exact sub_eq_zero.mp hz

private theorem normalized_integrand {t : ℝ} (ht : 0 < t) (w : ℂ) (a : ℝ) :
    cauchyKernel w t*epsteinField w (a/t)/(t : ℂ)=
      (averagingFactor w)⁻¹*(cauchyWeight w t*epsteinField w (a/t)) := by
  unfold cauchyKernel
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

private theorem convolution_eq_average (w : ℂ) (a : ℝ) :
    _root_.RHTower.positiveMellinConvolution (cauchyKernel w) (epsteinField w) a=
      (averagingFactor w)⁻¹*MayerEpsteinIntegral.average w a := by
  unfold MayerEpsteinIntegral.average
  rw [_root_.RHTower.positiveMellinConvolution,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => normalized_integrand ht w a),
    integral_const_mul]

/-- The continued, normalized Epstein convolution is absolutely convergent. -/
theorem cauchyKernel_epstein_integrable {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => cauchyKernel w t*epsteinField w (a/t)/(t : ℂ)) (Ioi 0) := by
  exact MeasureTheory.IntegrableOn.congr_fun
    ((average_integrable hw hw2 ha).const_mul (averagingFactor w)⁻¹)
    (fun t ht => (normalized_integrand ht w a).symm) measurableSet_Ioi

/-- The actual normalized Epstein convolution is holomorphic, including at parameter one. -/
theorem differentiableAt_convolution {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : 0 < a) :
    DifferentiableAt ℂ (fun v => _root_.RHTower.positiveMellinConvolution
      (cauchyKernel v) (epsteinField v) a) w := by
  simp only [convolution_eq_average]
  exact ((differentiableAt_averagingFactor hw).inv (averagingFactor_ne_zero_halfPlane hw)).mul
    (differentiableAt_average hw hw2 ha)

/-- The independently continued Epstein field maps to the actual Mayer scattering period. -/
theorem cauchyKernel_epstein_period {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : a ∈ MayerScatteringPeriod.periodSegment) :
    _root_.RHTower.positiveMellinConvolution (cauchyKernel w) (epsteinField w) a=
      MayerScatteringPeriod.periodValue w a := by
  rw [convolution_eq_average,average_eq_period hw hw2 ha,
    inv_mul_cancel_left₀ (averagingFactor_ne_zero_halfPlane hw)]

#print axioms sourceDomain_preconnected
#print axioms average_eq_period
#print axioms cauchyKernel_epstein_integrable
#print axioms differentiableAt_convolution
#print axioms cauchyKernel_epstein_period
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinContinuation
