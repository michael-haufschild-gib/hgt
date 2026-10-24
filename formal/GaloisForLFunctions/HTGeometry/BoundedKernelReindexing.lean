import GaloisForLFunctions.HTGeometry.PSDKernelOperations
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Bounded reindexing of kernel Gram spaces

A quadratic-form bound makes coefficient pushforward continuous for the kernel
seminorm. Completion then gives a bounded operator on the Gram Hilbert space.
The Gram vectors are total, so operators are determined by their action on them.
-/

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry
namespace KernelPre

variable {X : Type*} (K : X → X → ℂ)

/-- Push finite coefficients along an index map. -/
def pushforward (φ : X → X) : KernelPre K →ₗ[ℂ] KernelPre K :=
  Finsupp.lmapDomain ℂ ℂ φ

variable [Fact (IsPSDKernel K)]

/-- A quadratic-form bound controls the kernel seminorm, including its nullspace. -/
theorem norm_pushforward_le (φ : X → X) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => K (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) (c : KernelPre K) :
    ‖pushforward K φ c‖ ≤ C * ‖c‖ := by
  have hs : ‖pushforward K φ c‖ ^ 2 ≤ (C * ‖c‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_def, inner_def]
    change (kernelForm K (Finsupp.mapDomain φ c) (Finsupp.mapDomain φ c)).re ≤ _
    rw [kernelForm_mapDomain]
    exact h c
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    two_ne_zero).mp hs

/-- Bounded pushforward on the seminormed coefficient space. -/
def pushforwardL (φ : X → X) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => K (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) : KernelPre K →L[ℂ] KernelPre K :=
  (pushforward K φ).mkContinuous C (norm_pushforward_le K φ hC h)

end KernelPre

namespace KernelHilbert

variable {X : Type*} (K : X → X → ℂ) [Fact (IsPSDKernel K)]

/-- The canonical linear map from coefficients into their Gram completion. -/
def coeLinearMap : KernelPre K →ₗ[ℂ] KernelHilbert K where
  toFun c := c
  map_add' := UniformSpace.Completion.coe_add
  map_smul' := UniformSpace.Completion.coe_smul

theorem coe_single (x : X) (a : ℂ) :
    ((Finsupp.single x a : KernelPre K) : KernelHilbert K) = a • vector K x := by
  change coeLinearMap K (Finsupp.single x a) = a • coeLinearMap K (Finsupp.single x 1)
  rw [← map_smul]
  congr 1
  simp

/-- Every finite coefficient vector is in the span of the Gram vectors. -/
theorem coe_mem_span_vectors (c : KernelPre K) :
    (c : KernelHilbert K) ∈ Submodule.span ℂ (Set.range (vector K)) := by
  change coeLinearMap K c ∈ Submodule.span ℂ (Set.range (vector K))
  induction c using Finsupp.induction with
  | zero => simp
  | single_add x a c hx ha ih =>
    rw [map_add]
    refine Submodule.add_mem _ ?_ ih
    change ((Finsupp.single x a : KernelPre K) : KernelHilbert K) ∈ _
    rw [coe_single]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)

/-- The Gram vectors have dense linear span in their Hilbert realization. -/
theorem dense_span_vectors :
    Dense ((Submodule.span ℂ (Set.range (vector K)) : Submodule ℂ (KernelHilbert K)) :
      Set (KernelHilbert K)) := by
  apply (UniformSpace.Completion.denseRange_coe (α := KernelPre K)).mono
  rintro v ⟨c, rfl⟩
  exact coe_mem_span_vectors K c

/-- Continuous linear maps agree everywhere if they agree on every Gram vector. -/
theorem ext_on_vectors {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {L M : KernelHilbert K →L[ℂ] F}
    (h : ∀ x, L (vector K x) = M (vector K x)) : L = M := by
  ext v
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq L.continuous M.continuous
  | ih c =>
    change L (coeLinearMap K c) = M (coeLinearMap K c)
    induction c using Finsupp.induction with
    | zero => simp
    | single_add x a c hx ha ih =>
      simp only [map_add, ih]
      congr 1
      change L ((Finsupp.single x a : KernelPre K) : KernelHilbert K) =
        M ((Finsupp.single x a : KernelPre K) : KernelHilbert K)
      simp only [coe_single, map_smul, h]

/-- The bounded reindexing operator on the Gram Hilbert space. -/
def pushforward (φ : X → X) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => K (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) : KernelHilbert K →L[ℂ] KernelHilbert K :=
  (KernelPre.pushforwardL K φ hC h).completion

theorem pushforward_coe (φ : X → X) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => K (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) (c : KernelPre K) :
    pushforward K φ hC h (c : KernelHilbert K) =
      ((KernelPre.pushforward K φ c : KernelPre K) : KernelHilbert K) := by
  exact ContinuousLinearMap.completion_apply_coe _ c

/-- The completed operator reindexes each generating vector exactly. -/
theorem pushforward_vector (φ : X → X) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => K (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) (x : X) :
    pushforward K φ hC h (vector K x) = vector K (φ x) := by
  rw [vector, pushforward_coe]
  congr 1
  exact Finsupp.mapDomain_single

theorem norm_pushforward_apply_le (φ : X → X) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => K (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) (v : KernelHilbert K) :
    ‖pushforward K φ hC h v‖ ≤ C * ‖v‖ := by
  induction v using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le ((pushforward K φ hC h).continuous.norm)
      (continuous_const.mul continuous_norm)
  | ih c =>
    rw [pushforward_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact KernelPre.norm_pushforward_le K φ hC h c

/-- Completion preserves the coefficient-space operator bound. -/
theorem norm_pushforward_le (φ : X → X) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : X →₀ ℂ,
      (kernelForm (fun x y => K (φ x) (φ y)) c c).re ≤
        C ^ 2 * (kernelForm K c c).re) :
    ‖pushforward K φ hC h‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_pushforward_apply_le K φ hC h)

end KernelHilbert
end GaloisForLFunctions.HTGeometry

