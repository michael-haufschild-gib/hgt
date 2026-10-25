import GaloisForLFunctions.HTGeometry.BoundedKernelReindexing

/-!
# Dominated kernels have bounded feature comparisons

A quadratic-form domination passes through the kernel null quotient and
completion, giving a bounded linear comparison with the prescribed values
on all feature vectors.
-/

section

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry
namespace KernelPre
variable {X Y : Type*} (K : X → X → ℂ) (L : Y → Y → ℂ)

/-- Coefficients reindexed between two distinct Gram coefficient spaces. -/
def coefficientComparison (φ : X → Y) : KernelPre K →ₗ[ℂ] KernelPre L :=
  Finsupp.lmapDomain ℂ ℂ φ

variable [Fact (IsPSDKernel K)] [Fact (IsPSDKernel L)]

/-- Domination of pulled-back kernel forms gives a bounded comparison of coefficient norms. -/
theorem norm_coefficientComparison_le (φ : X → Y) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => L (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) (c : KernelPre K) :
    ‖coefficientComparison K L φ c‖ ≤ C * ‖c‖ := by
  have hs : ‖coefficientComparison K L φ c‖ ^ 2 ≤ (C * ‖c‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_def, inner_def]
    change (kernelForm L (Finsupp.mapDomain φ c) (Finsupp.mapDomain φ c)).re ≤ _
    rw [kernelForm_mapDomain]
    exact h c
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    two_ne_zero).mp hs

def coefficientComparisonL (φ : X → Y) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => L (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) : KernelPre K →L[ℂ] KernelPre L :=
  (coefficientComparison K L φ).mkContinuous C (norm_coefficientComparison_le K L φ hC h)

end KernelPre

namespace KernelHilbert
variable {X Y : Type*} (K : X → X → ℂ) (L : Y → Y → ℂ)
  [Fact (IsPSDKernel K)] [Fact (IsPSDKernel L)]

/-- A dominated kernel gives a continuous comparison between its completed Gram spaces. -/
def comparison (φ : X → Y) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => L (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) : KernelHilbert K →L[ℂ] KernelHilbert L :=
  (KernelPre.coefficientComparisonL K L φ hC h).completion

theorem comparison_vector (φ : X → Y) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => L (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) (x : X) :
    comparison K L φ hC h (vector K x) = vector L (φ x) := by
  rw [vector, comparison, ContinuousLinearMap.completion_apply_coe]
  congr 1
  exact Finsupp.mapDomain_single

theorem norm_comparison_apply_le (φ : X → Y) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => L (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) (v : KernelHilbert K) :
    ‖comparison K L φ hC h v‖ ≤ C * ‖v‖ := by
  induction v using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le ((comparison K L φ hC h).continuous.norm)
      (continuous_const.mul continuous_norm)
  | ih c =>
    rw [comparison, ContinuousLinearMap.completion_apply_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact KernelPre.norm_coefficientComparison_le K L φ hC h c

theorem norm_comparison_le (φ : X → Y) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => L (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) : ‖comparison K L φ hC h‖ ≤ C :=
  (comparison K L φ hC h).opNorm_le_bound hC (norm_comparison_apply_le K L φ hC h)

end KernelHilbert
end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.KernelHilbert.comparison_vector
#print axioms GaloisForLFunctions.HTGeometry.KernelHilbert.norm_comparison_le
end
end
