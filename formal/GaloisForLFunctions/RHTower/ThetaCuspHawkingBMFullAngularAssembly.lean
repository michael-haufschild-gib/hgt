import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalCuspCutoff
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularLaplacian

/-!
The complete angular response is globally smooth and modular invariant and solves the original squared-source equation at every point. Subtracting the original cusp cutoff recovers the constructed native energy response.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

private theorem chartLaplacian_add (f g : UpperHalfPlane → ℂ)
    (hf : ChartSmooth f) (hg : ChartSmooth g) (z : UpperHalfPlane) :
    chartLaplacian (fun w => f w+g w) z = chartLaplacian f z+chartLaplacian g z := by
  let F := f ∘ ofComplex
  let G := g ∘ ofComplex
  have hd (i : Fin 2) :
      fderiv ℝ (fun w => fderiv ℝ (fun w => F w+G w) w (direction i)) (z:ℂ) (direction i) =
        fderiv ℝ (fun w => fderiv ℝ F w (direction i)) (z:ℂ) (direction i) +
        fderiv ℝ (fun w => fderiv ℝ G w (direction i)) (z:ℂ) (direction i) := by
    have he : (fun w => fderiv ℝ (fun w => F w+G w) w (direction i)) =ᶠ[𝓝 (z:ℂ)]
        (fun w => fderiv ℝ F w (direction i)+fderiv ℝ G w (direction i)) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
      rw [fderiv_fun_add ((hf ⟨w,hw⟩).differentiableAt (by simp))
        ((hg ⟨w,hw⟩).differentiableAt (by simp)),add_apply]
    have hF : DifferentiableAt ℝ (fun w => fderiv ℝ F w (direction i)) (z:ℂ) := (((hf z).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
    have hG : DifferentiableAt ℝ (fun w => fderiv ℝ G w (direction i)) (z:ℂ) := (((hg z).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
    rw [he.fderiv_eq,fderiv_fun_add hF hG,add_apply]
  change (z.im : ℂ)^(2 : ℕ)*(∑ i : Fin 2,
    fderiv ℝ (fun w => fderiv ℝ (fun w => F w+G w) w (direction i)) (z:ℂ) (direction i)) = _
  rw [Finset.sum_congr rfl (fun i _ => hd i),Finset.sum_add_distrib,mul_add]
  rfl

private theorem globalCuspCutoff_forcing_on_fd (q : XiZeroCopy) (branch : Bool)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    chartLaplacian (globalCuspCutoff q branch) z - parameter q branch*globalCuspCutoff q branch z +
      globalForcing q branch z = (parameter q branch/2)*scalar (center q) (coordinates z)^(2 : ℕ) := by
  rw [chartLaplacian_congr (globalCuspCutoff_germ q branch z hz),chartLaplacian_coordinates,
    globalCuspCutoff_eq_on_fd q branch z hz,globalForcing_eq_on_fd q branch z hz]
  unfold forcing
  ring

/-- The global cusp extension retains the entire original differential forcing at every point. -/
theorem globalCuspCutoff_forcing_equation (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane) :
    chartLaplacian (globalCuspCutoff q branch) z - parameter q branch*globalCuspCutoff q branch z +
      globalForcing q branch z = (parameter q branch/2)*scalar (center q) (coordinates z)^(2 : ℕ) := by
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  have he := globalCuspCutoff_forcing_on_fd q branch (A • z) hA
  have hD := chartLaplacian_invariant _ (globalCuspCutoff_smooth q branch)
    (globalCuspCutoff_invariant q branch) (QuotientGroup.mk A) z
  have hK := globalCuspCutoff_invariant q branch (QuotientGroup.mk A) z
  have hF := globalForcing_invariant q branch (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at hD hK hF
  rw [hD,hK,hF,xi_scalar_modular] at he
  exact he

/-- The full angular response: original global cusp principal response plus the actual forced correction. -/
def fullAngular (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane) : ℂ :=
  globalCuspCutoff q branch z+globalResponse q branch z

/-- The complete original angular response is globally smooth across every modular seam. -/
theorem fullAngular_smooth (q : XiZeroCopy) (branch : Bool) : ChartSmooth (fullAngular q branch) := by
  intro z
  exact (globalCuspCutoff_smooth q branch z).add (globalResponse_smooth q branch z)

/-- The complete original angular response is pointwise modular invariant. -/
theorem fullAngular_invariant (q : XiZeroCopy) (branch : Bool) (γ : PSL2Z) (z : UpperHalfPlane) :
    fullAngular q branch (γ • z) = fullAngular q branch z := by
  simp only [fullAngular,globalCuspCutoff_invariant,globalResponse_invariant]

/-- The assembled actual field solves the original full squared-source angular equation everywhere. -/
theorem fullAngular_classical_equation (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane) :
    chartLaplacian (fullAngular q branch) z - parameter q branch*fullAngular q branch z =
      (parameter q branch/2)*scalar (center q) (coordinates z)^(2 : ℕ) := by
  have hK := globalCuspCutoff_forcing_equation q branch z
  have hR := globalResponse_classical_equation q branch z
  change chartLaplacian (fun w => globalCuspCutoff q branch w+globalResponse q branch w) z -
    parameter q branch*(globalCuspCutoff q branch z+globalResponse q branch z) = _
  rw [chartLaplacian_add _ _ (globalCuspCutoff_smooth q branch)
    (globalResponse_smooth q branch)]
  linear_combination hK+hR

/-- Subtracting the original complete cusp cutoff recovers the actual native Hilbert-space correction. -/
theorem fullAngular_renormalized_native (q : XiZeroCopy) (branch : Bool) :
    (fun z => fullAngular q branch z-cutoffResponse q branch (coordinates z)) =ᵐ[measure]
      embedding (weakResponse q branch) := by
  filter_upwards [ae_mem_interior,globalResponse_native_ae q branch] with z hz hr
  rw [fullAngular,globalCuspCutoff_eq_on_fd q branch z (fdo_subset_fd hz),add_sub_cancel_left,hr]

end
end RHTower.D4BMModularCore
