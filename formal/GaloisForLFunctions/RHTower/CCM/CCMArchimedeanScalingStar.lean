import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanIntegratedScaling
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Star law for the archimedean integrated scaling representation

This module equips logarithmic Haar kernels with source involution
g-star(u) = conjugate(g(-u)) and proves rho(g)† = rho(g-star) unconditionally.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Haar reflection u ↦ -u on logarithmic test kernels. -/
def ccmLogKernelReflect (g : CCMLogKernel) : CCMLogKernel :=
  Lp.compMeasurePreserving (fun u : ℝ => -u)
    (Measure.measurePreserving_neg (volume : Measure ℝ)) g

theorem ccmLogKernelReflect_ae (g : CCMLogKernel) :
    (ccmLogKernelReflect g : ℝ → ℂ) =ᵐ[volume] fun u : ℝ => g (-u) := by
  exact Lp.coeFn_compMeasurePreserving g
    (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- Convolution-algebra involution g-star(u) = conjugate(g(-u)). -/
def ccmLogKernelStar (g : CCMLogKernel) : CCMLogKernel :=
  star (ccmLogKernelReflect g)

theorem ccmLogKernelStar_ae (g : CCMLogKernel) :
    (ccmLogKernelStar g : ℝ → ℂ) =ᵐ[volume]
      fun u : ℝ => starRingEnd ℂ (g (-u)) := by
  change ((star (ccmLogKernelReflect g) : CCMLogKernel) : ℝ → ℂ) =ᵐ[volume]
    fun u : ℝ => starRingEnd ℂ (g (-u))
  filter_upwards [Lp.coeFn_star (ccmLogKernelReflect g), ccmLogKernelReflect_ae g]
    with u hstar href
  rw [hstar, Pi.star_apply, href]
  rfl

@[simp] theorem norm_ccmLogKernelReflect (g : CCMLogKernel) :
    ‖ccmLogKernelReflect g‖ = ‖g‖ :=
  Lp.norm_compMeasurePreserving g
    (Measure.measurePreserving_neg (volume : Measure ℝ))

@[simp] theorem norm_ccmLogKernelStar (g : CCMLogKernel) :
    ‖ccmLogKernelStar g‖ = ‖g‖ := by
  calc
    ‖ccmLogKernelStar g‖ = ‖ccmLogKernelReflect g‖ := by
      rw [ccmLogKernelStar, Lp.norm_def, Lp.norm_def]
      exact congrArg ENNReal.toReal
        (AEEqFun.eLpNorm_star
          (f := (ccmLogKernelReflect g : ℝ →ₘ[volume] ℂ)))
    _ = ‖g‖ := norm_ccmLogKernelReflect g

@[simp] theorem ccmLogKernelStar_star (g : CCMLogKernel) :
    ccmLogKernelStar (ccmLogKernelStar g) = g := by
  apply Lp.ext
  have hinner := (ccmLogKernelStar_ae g).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [ccmLogKernelStar_ae (ccmLogKernelStar g), hinner] with u hout hin
  simp only [Function.comp_apply] at hin
  rw [hout, hin]
  simp

/-- Source scaling at one logarithmic group parameter as a bounded operator. -/
def ccmLogDilationOperator (u : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  (evenDilationUnitary (Real.exp (-u)) (Real.exp_pos (-u)) :
    evenSubspace →L[ℂ] evenSubspace)

@[simp] theorem ccmLogDilationOperator_apply (u : ℝ) (f : evenSubspace) :
    ccmLogDilationOperator u f = ccmLogDilationOrbit f u := rfl

/-- Unitary source law U(u)† = U(-u). -/
theorem adjoint_ccmLogDilationOperator (u : ℝ) :
    ContinuousLinearMap.adjoint (ccmLogDilationOperator u) =
      ccmLogDilationOperator (-u) := by
  rw [ccmLogDilationOperator, LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change dilation (Real.exp (-u))⁻¹ (inv_pos.mpr (Real.exp_pos (-u))) (f : SoninL2) =
    dilation (Real.exp (- -u)) (Real.exp_pos (- -u)) (f : SoninL2)
  apply Lp.ext
  filter_upwards [
    dilation_ae (Real.exp (-u))⁻¹ (inv_pos.mpr (Real.exp_pos (-u))) (f : SoninL2),
    dilation_ae (Real.exp (- -u)) (Real.exp_pos (- -u)) (f : SoninL2)
  ] with x hleft hright
  rw [hleft, hright]
  have hscale : (Real.exp (-u))⁻¹ = Real.exp (- -u) := by
    rw [← Real.exp_neg]
  rw [hscale]

theorem inner_ccmLogDilationOrbit (u : ℝ) (x y : evenSubspace) :
    ⟪ccmLogDilationOrbit x (-u), y⟫_ℂ = ⟪x, ccmLogDilationOrbit y u⟫_ℂ := by
  have h := ContinuousLinearMap.adjoint_inner_left (ccmLogDilationOperator u) y x
  rw [adjoint_ccmLogDilationOperator] at h
  simpa using h

private theorem integral_inner_const_ccm {F : ℝ → evenSubspace}
    (hF : Integrable F volume) (x : evenSubspace) :
    (∫ u : ℝ, ⟪F u, x⟫_ℂ) = ⟪∫ u : ℝ, F u, x⟫_ℂ := by
  calc
    (∫ u : ℝ, ⟪F u, x⟫_ℂ)
        = ∫ u : ℝ, starRingEnd ℂ ⟪x, F u⟫_ℂ := by
          apply integral_congr_ae
          filter_upwards [] with u
          exact (inner_conj_symm (𝕜 := ℂ) (F u) x).symm
    _ = starRingEnd ℂ (∫ u : ℝ, ⟪x, F u⟫_ℂ) := integral_conj
    _ = starRingEnd ℂ ⟪x, ∫ u : ℝ, F u⟫_ℂ := by
      rw [integral_inner hF x]
    _ = ⟪∫ u : ℝ, F u, x⟫_ℂ := inner_conj_symm (𝕜 := ℂ) _ _

/-- Exact source involution law for integrated scaling: rho(g)† = rho(g-star). -/
theorem adjoint_ccmIntegratedScaling (g : CCMLogKernel) :
    ContinuousLinearMap.adjoint (ccmIntegratedScaling g) =
      ccmIntegratedScaling (ccmLogKernelStar g) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [ccmIntegratedScaling_apply]
  rw [← integral_inner_const_ccm (integrable_ccmLogKernel_smul_orbit g y) x]
  rw [← integral_inner (integrable_ccmLogKernel_smul_orbit (ccmLogKernelStar g) x) y]
  let F : ℝ → ℂ := fun u =>
    starRingEnd ℂ (g u) * ⟪ccmLogDilationOrbit y u, x⟫_ℂ
  calc
    (∫ u : ℝ, ⟪g u • ccmLogDilationOrbit y u, x⟫_ℂ)
        = ∫ u : ℝ, F u := by
          apply integral_congr_ae
          filter_upwards [] with u
          exact inner_smul_left (ccmLogDilationOrbit y u) x (g u)
    _ = ∫ u : ℝ, F (-u) := by
      symm
      exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding F
    _ = ∫ u : ℝ,
        ⟪y, ccmLogKernelStar g u • ccmLogDilationOrbit x u⟫_ℂ := by
      apply integral_congr_ae
      filter_upwards [ccmLogKernelStar_ae g] with u hstar
      rw [hstar]
      simp only [F]
      rw [inner_ccmLogDilationOrbit u y x]
      exact (inner_smul_right y (ccmLogDilationOrbit x u)
        (starRingEnd ℂ (g (-u)))).symm

end RHTower
