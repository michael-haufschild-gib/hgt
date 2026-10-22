import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAngularTwoWeight
import GaloisForLFunctions.HTGeometry.DbarSolve
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Compact evaluation of the actual tensor polarizations

A smooth divided-cutoff Wirtinger kernel reconstructs every holomorphic field
on a unit ball. The kernel is smooth even at its center, has fixed compact
support, and translates without changing its profile. It evaluates both actual
complex tensor polarizations, with their exact factor of pi.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped ContDiff
namespace RHTower.D4BMAngularTwoCuspTest
open _root_.HTGeometry
noncomputable section
set_option autoImplicit false

def cutoffBump : ContDiffBump (0:ℂ) := ⟨1/8,1/4,by norm_num,by norm_num⟩
def cutoff (z : ℂ) : ℂ := (cutoffBump z : ℂ)

theorem cutoff_smooth : ContDiff ℝ ∞ cutoff :=
  Complex.ofRealCLM.contDiff.comp cutoffBump.contDiff

theorem cutoff_compact : HasCompactSupport cutoff :=
  cutoffBump.hasCompactSupport.comp_left rfl

theorem cutoff_support : tsupport cutoff ⊆ closedBall 0 (1/4) := by
  apply (tsupport_comp_subset (g := Complex.ofReal) rfl cutoffBump).trans
  rw [cutoffBump.tsupport_eq]
  exact Subset.rfl

private theorem cutoff_one {z : ℂ} (hz : ‖z‖ ≤ 1/8) : cutoff z = 1 := by
  have hb : cutoffBump z = 1 := cutoffBump.one_of_mem_closedBall (by
    simpa only [mem_closedBall,dist_zero_right,cutoffBump] using hz)
  simp only [cutoff,hb,Complex.ofReal_one]

private theorem cutoff_dbar_eq : dzbar cutoff = wirtingerAntiholL ∘ fderiv ℝ cutoff := by
  funext z
  exact (wirtingerAntiholL_apply _).symm

private theorem cutoff_dbar_smooth : ContDiff ℝ ∞ (dzbar cutoff) := by
  rw [cutoff_dbar_eq]
  exact wirtingerAntiholL.contDiff.comp (cutoff_smooth.fderiv_right (m := ∞) (by simp))

private theorem cutoff_dbar_support : tsupport (dzbar cutoff) ⊆ tsupport cutoff := by
  rw [cutoff_dbar_eq]
  exact (tsupport_comp_subset (map_zero wirtingerAntiholL) _).trans (tsupport_fderiv_subset ℝ)

private theorem cutoff_dbar_zero {z : ℂ} (hz : ‖z‖ < 1/8) : dzbar cutoff z = 0 := by
  have he : cutoff =ᶠ[𝓝 z] (fun _ => (1:ℂ)) := by
    filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball (0:ℂ) (1/8) by
      simpa only [mem_ball,dist_zero_right] using hz)] with w hw
    exact cutoff_one (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hw))
  rw [dzbar,he.fderiv_eq]
  simp [wirtingerAntihol]

/-- A fixed smooth Cauchy evaluation kernel, with its singularity removed by the cutoff. -/
def kernel (z : ℂ) : ℂ := dzbar cutoff z / (-z)

theorem kernel_smooth : ContDiff ℝ ∞ kernel := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply ContDiffAt.congr_of_eventuallyEq contDiffAt_const
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0:ℝ)<1/8))] with w hw
    change kernel w = (0:ℂ)
    rw [kernel,cutoff_dbar_zero (by simpa only [mem_ball,dist_zero_right] using hw),zero_div]
  · unfold kernel
    simp only [div_eq_mul_inv]
    exact cutoff_dbar_smooth.contDiffAt.mul
      ((contDiffAt_id.neg : ContDiffAt ℝ ∞ (fun w : ℂ => -w) z).fun_inv (neg_ne_zero.mpr hz))

theorem kernel_support : tsupport kernel ⊆ closedBall 0 (1/4) := by
  apply (closure_mono (show Function.support kernel ⊆ Function.support (dzbar cutoff) from by
    intro z hz hn
    exact hz (by simp only [kernel,hn,zero_div]))).trans
  exact cutoff_dbar_support.trans cutoff_support

theorem kernel_compact : HasCompactSupport kernel :=
  (isCompact_closedBall (0:ℂ) (1/4)).of_isClosed_subset (isClosed_tsupport kernel) kernel_support

private theorem cutoff_mul_smooth (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1)) :
    ContDiff ℝ 1 (fun z => cutoff z*F z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ ball (0:ℂ) 1
  · exact ((contDiff_infty.mp cutoff_smooth) 1).contDiffAt.mul
      (((hF.analyticOnNhd isOpen_ball z hz).contDiffAt).restrict_scalars ℝ)
  · have hn : z ∉ tsupport cutoff := by
      intro ht
      have hh := cutoff_support ht
      simp only [mem_closedBall,dist_zero_right] at hh
      exact hz (by simp only [mem_ball,dist_zero_right]; linarith)
    apply ContDiffAt.congr_of_eventuallyEq contDiffAt_const
    filter_upwards [(isClosed_tsupport cutoff).isOpen_compl.mem_nhds hn] with w hw
    rw [image_eq_zero_of_notMem_tsupport hw,zero_mul]

private theorem cutoff_mul_dbar (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1)) (z : ℂ) :
    dzbar (fun w => cutoff w*F w) z = dzbar cutoff z*F z := by
  by_cases hz : z ∈ ball (0:ℂ) 1
  · have hd := hF.differentiableAt (isOpen_ball.mem_nhds hz)
    have hf := hd.restrictScalars ℝ
    have he := (dzbar_eq_zero_of_differentiableAt hd).1
    unfold dzbar wirtingerAntihol at he ⊢
    rw [fderiv_fun_mul (cutoff_smooth.differentiable (by simp) z) hf]
    simp only [add_apply,smul_apply,smul_eq_mul]
    linear_combination cutoff z*he
  · have hn : z ∉ tsupport cutoff := by
      intro ht
      have hh := cutoff_support ht
      simp only [mem_closedBall,dist_zero_right] at hh
      exact hz (by simp only [mem_ball,dist_zero_right]; linarith)
    have he : (fun w => cutoff w*F w) =ᶠ[𝓝 z] (fun _ => (0:ℂ)) := by
      filter_upwards [(isClosed_tsupport cutoff).isOpen_compl.mem_nhds hn] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw,zero_mul]
    have hd : dzbar cutoff z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hn (cutoff_dbar_support ht))
    rw [dzbar,he.fderiv_eq,hd]
    simp [wirtingerAntihol]

/-- This fixed compact kernel recovers every holomorphic field on its original local disk. -/
theorem kernel_evaluation (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1)) :
    (∫ w : ℂ, kernel w*F w) = (Real.pi:ℂ)*F 0 := by
  have hk : HasCompactSupport (fun w => cutoff w*F w) := cutoff_compact.mul_right
  have he := integral_dzbar_kernel (cutoff_mul_smooth F hF) hk (0:ℂ)
  have hs := integral_sub_left_eq_self
    (fun u : ℂ => dzbar (fun w => cutoff w*F w) u / (-u)) volume (0:ℂ)
  simp only [zero_sub,neg_neg] at hs he
  rw [hs] at he
  simp only [cutoff_mul_dbar F hF,cutoff_one (z := 0) (by simp),one_mul,Complex.real_smul] at he
  calc
    _ = ∫ w : ℂ, dzbar cutoff w*F w / (-w) := by
      apply integral_congr_ae
      filter_upwards [] with w
      unfold kernel
      ring
    _ = _ := he

/-- Translation preserves the fixed compact holomorphic evaluation formula. -/
theorem kernel_translated_evaluation (F : ℂ → ℂ) (c : ℂ)
    (hF : DifferentiableOn ℂ F (ball c 1)) :
    (∫ w : ℂ, kernel (w-c)*F w) = (Real.pi:ℂ)*F c := by
  have hh : DifferentiableOn ℂ (fun w => F (w+c)) (ball 0 1) := by
    intro w hw
    have hm : w+c ∈ ball c 1 := by
      simpa only [mem_ball,dist_eq_norm,add_sub_cancel_right,sub_zero] using hw
    exact ((hF.differentiableAt (isOpen_ball.mem_nhds hm)).comp w
      (differentiableAt_id.add_const c)).differentiableWithinAt
  have he := kernel_evaluation (fun w => F (w+c)) hh
  have hs := integral_add_right_eq_self (μ := (volume : Measure ℂ)) (fun w : ℂ => kernel (w-c)*F w) c
  simp only [add_sub_cancel_right,zero_add] at hs he
  exact hs.symm.trans he


open UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open D4BMModularCore D4BMAngularTwo

/-- Every translated kernel has the same fixed support radius. -/
theorem translated_kernel_support (c : ℂ) :
    tsupport (fun w => kernel (w-c)) ⊆ closedBall c (1/4) := by
  intro w hw
  have ht := tsupport_comp_subset_preimage kernel (continuous_id.sub continuous_const) hw
  have hb := kernel_support ht
  simpa only [mem_closedBall,dist_eq_norm,sub_zero,Pi.sub_apply,id_eq] using hb

/-- The original compact evaluation kernel as an admitted positive-height chart test. -/
def kernelTest (c : ℂ) (hc : 1 < c.im) : PlanarChartTest where
  field w := kernel (w-c)
  smooth := kernel_smooth.comp (contDiff_id.sub contDiff_const)
  compact := kernel_compact.comp_homeomorph (Homeomorph.subRight c)
  support := by
    intro w hw
    have hb := translated_kernel_support c hw
    rw [mem_closedBall,dist_eq_norm] at hb
    have hi := (Complex.abs_im_le_norm (w-c)).trans hb
    rw [Complex.sub_im] at hi
    have hlo := (abs_le.mp hi).1
    change 0 < w.im
    linarith

private theorem ball_positive (c : ℂ) (hc : 1 < c.im) :
    ball c 1 ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  rw [mem_ball,dist_eq_norm] at hw
  have hi := (Complex.abs_im_le_norm (w-c)).trans_lt hw
  rw [Complex.sub_im] at hi
  have hlo := (abs_lt.mp hi).1
  change 0 < w.im
  linarith

/-- The fixed admitted test recovers the first actual tensor polarization. -/
theorem holomorphicPolarization_evaluation (q : XiZeroCopy) (c : ℂ) (hc : 1 < c.im) :
    (∫ w : ℂ, (kernelTest c hc).field w*D4BMAngularTwoTensor.holomorphicPolarization q w) =
      (Real.pi:ℂ)*D4BMAngularTwoTensor.holomorphicPolarization q c := by
  apply kernel_translated_evaluation
  intro w hw
  exact (D4BMAngularTwoTensor.holomorphicPolarization_differentiableAt q w
    (ball_positive c hc hw)).differentiableWithinAt

/-- The same fixed test recovers the independent conjugate polarization. -/
theorem conjugatePolarization_evaluation (q : XiZeroCopy) (c : ℂ) (hc : 1 < c.im) :
    (∫ w : ℂ, (kernelTest c hc).field w*D4BMAngularTwoTensor.conjugatePolarization q w) =
      (Real.pi:ℂ)*D4BMAngularTwoTensor.conjugatePolarization q c := by
  apply kernel_translated_evaluation
  intro w hw
  exact (D4BMAngularTwoTensor.conjugatePolarization_differentiableAt q w
    (ball_positive c hc hw)).differentiableWithinAt


end
end RHTower.D4BMAngularTwoCuspTest
