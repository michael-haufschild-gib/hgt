import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanScalingStar
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Prod

/-!
# The convolution law for the archimedean CCM representation

The logarithmic form of the multiplicative Haar group is the additive group `ℝ`.  This file
bundles the ordinary Haar convolution of two intrinsic `L¹` kernels and proves the exact integrated
representation law

`rho(g * h) = rho(g) rho(h)`.

The proof is not an abstract representation hypothesis: it expands both Bochner integrals, proves
the joint kernel integrable, and uses the measure-preserving shear `(u,v) ↦ (u,u+v)`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped Convolution InnerProductSpace

noncomputable section

namespace RHTower

private theorem integrable_ccmLogKernelRawConvolution
    (g h : CCMLogKernel) :
    Integrable
      ((g : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (h : ℝ → ℂ))
      volume :=
  (L1.integrable_coeFn g).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (L1.integrable_coeFn h)

/-- Additive Haar convolution on logarithmic CCM source kernels. -/
def ccmLogKernelConvolution (g h : CCMLogKernel) : CCMLogKernel :=
  (integrable_ccmLogKernelRawConvolution g h).toL1
    ((g : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (h : ℝ → ℂ))

theorem ccmLogKernelConvolution_ae (g h : CCMLogKernel) :
    (ccmLogKernelConvolution g h : ℝ → ℂ) =ᵐ[volume]
      fun w : ℝ ↦ ∫ u : ℝ, g u * h (w - u) := by
  exact (integrable_ccmLogKernelRawConvolution g h).coeFn_toL1

private theorem integrable_ccmIntegratedScalingProductKernel
    (g h : CCMLogKernel) (f : evenSubspace) :
    Integrable
      (fun p : ℝ × ℝ ↦
        (g p.1 * h p.2) • ccmLogDilationOrbit f (p.1 + p.2))
      (volume.prod volume) := by
  have hscalar : Integrable (fun p : ℝ × ℝ ↦ g p.1 * h p.2)
      (volume.prod volume) := by
    exact Integrable.op_fst_snd continuous_mul
      ⟨1, fun x y : ℂ ↦ by simp⟩
      (L1.integrable_coeFn g) (L1.integrable_coeFn h)
  have horbit : Continuous
      (fun p : ℝ × ℝ ↦ ccmLogDilationOrbit f (p.1 + p.2)) :=
    (continuous_ccmLogDilationOrbit f).comp (continuous_fst.add continuous_snd)
  refine Integrable.mono' (hscalar.norm.mul_const ‖f‖)
    (hscalar.aestronglyMeasurable.smul horbit.aestronglyMeasurable) ?_
  filter_upwards [] with p
  rw [norm_smul, norm_ccmLogDilationOrbit]

private theorem integrable_ccmIntegratedScalingConvolutionKernel
    (g h : CCMLogKernel) (f : evenSubspace) :
    Integrable
      (fun p : ℝ × ℝ ↦
        (g p.1 * h (p.2 - p.1)) • ccmLogDilationOrbit f p.2)
      (volume.prod volume) := by
  have hprod := integrable_ccmIntegratedScalingProductKernel g h f
  have hshear :=
    (measurePreserving_prod_sub (volume : Measure ℝ) (volume : Measure ℝ)).integrable_comp_of_integrable
      hprod
  refine hshear.congr (Eventually.of_forall fun p => ?_)
  simp only [Function.comp_apply]
  rw [show p.1 + (p.2 - p.1) = p.2 by abel]

private theorem ccmIntegratedScaling_convolution_apply
    (g h : CCMLogKernel) (f : evenSubspace) :
    ccmIntegratedScaling (ccmLogKernelConvolution g h) f =
      ccmIntegratedScaling g (ccmIntegratedScaling h f) := by
  let A : ℝ × ℝ → evenSubspace := fun p ↦
    (g p.1 * h p.2) • ccmLogDilationOrbit f (p.1 + p.2)
  let B : ℝ × ℝ → evenSubspace := fun p ↦
    (g p.1 * h (p.2 - p.1)) • ccmLogDilationOrbit f p.2
  have hA : Integrable A (volume.prod volume) :=
    integrable_ccmIntegratedScalingProductKernel g h f
  have hB : Integrable B (volume.prod volume) :=
    integrable_ccmIntegratedScalingConvolutionKernel g h f
  have hconv := ccmLogKernelConvolution_ae g h
  calc
    ccmIntegratedScaling (ccmLogKernelConvolution g h) f
        = ∫ w : ℝ, (ccmLogKernelConvolution g h w) •
            ccmLogDilationOrbit f w := rfl
    _ = ∫ w : ℝ, (∫ u : ℝ, g u * h (w - u)) •
            ccmLogDilationOrbit f w := by
      apply integral_congr_ae
      filter_upwards [hconv] with w hw
      rw [hw]
    _ = ∫ w : ℝ, ∫ u : ℝ, B (u, w) := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [← integral_smul_const]
      rfl
    _ = ∫ u : ℝ, ∫ w : ℝ, B (u, w) :=
      (integral_integral_swap hB).symm
    _ = ∫ u : ℝ, ∫ v : ℝ, A (u, v) := by
      apply integral_congr_ae
      filter_upwards [] with u
      calc
        (∫ w : ℝ, B (u, w)) = ∫ v : ℝ, B (u, u + v) := by
          simpa only [add_comm] using
            (integral_add_left_eq_self (fun w : ℝ ↦ B (u, w)) u).symm
        _ = ∫ v : ℝ, A (u, v) := by
          apply integral_congr_ae
          filter_upwards [] with v
          simp only [A, B, add_sub_cancel_left]
    _ = ∫ u : ℝ, g u •
          ccmLogDilationOrbit (ccmIntegratedScaling h f) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [ccmIntegratedScaling_apply]
      have hmap := (ccmLogDilationOperator u).integral_comp_comm
        (integrable_ccmLogKernel_smul_orbit h f)
      change
        (∫ v : ℝ, A (u, v)) =
          g u • ccmLogDilationOperator u
            (∫ v : ℝ, h v • ccmLogDilationOrbit f v)
      rw [← hmap, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [A, map_smul, ccmLogDilationOperator_apply, smul_smul]
      rw [ccmLogDilationOrbit_add]
    _ = ccmIntegratedScaling g (ccmIntegratedScaling h f) := rfl

/-- Exact integrated representation law on intrinsic logarithmic `L¹` Haar kernels. -/
theorem ccmIntegratedScaling_convolution (g h : CCMLogKernel) :
    ccmIntegratedScaling (ccmLogKernelConvolution g h) =
      ccmIntegratedScaling g ∘L ccmIntegratedScaling h := by
  apply ContinuousLinearMap.ext
  intro f
  exact ccmIntegratedScaling_convolution_apply g h f

/-- The source product `g * g★` acts by the positive algebraic square `rho(g) rho(g)†`. -/
theorem ccmIntegratedScaling_convolution_star (g : CCMLogKernel) :
    ccmIntegratedScaling
        (ccmLogKernelConvolution g (ccmLogKernelStar g)) =
      ccmIntegratedScaling g ∘L
        ContinuousLinearMap.adjoint (ccmIntegratedScaling g) := by
  rw [ccmIntegratedScaling_convolution, adjoint_ccmIntegratedScaling]

end RHTower
