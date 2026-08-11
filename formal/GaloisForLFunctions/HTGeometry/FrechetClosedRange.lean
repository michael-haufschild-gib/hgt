import GaloisForLFunctions.HTGeometry.FrechetOpenMapping

/-!
# A closed range makes an injective map an embedding

If a continuous injective linear map between Fréchet spaces has closed range, its corestriction to
that range is a continuous linear bijection between Fréchet spaces, hence a homeomorphism.  So an
injective map whose inverse on the range is discontinuous cannot have closed range.

* `rangeEquiv` : the corestriction to the range.
* `continuous_rangeEquiv_symm_of_isClosed` : **the inverse on a closed range is continuous.**
-/

namespace GaloisForLFunctions

open Filter Set Topology Uniformity

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul 𝕜 E] [CompleteSpace E] [FirstCountableTopology E]
variable [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F]
  [ContinuousSMul 𝕜 F] [T2Space F] [TopologicalSpace.PseudoMetrizableSpace F]

/-- The corestriction of an injective linear map to its range. -/
noncomputable def rangeEquiv (f : E →ₗ[𝕜] F) (hinj : Function.Injective f) :
    E ≃ₗ[𝕜] ↥(LinearMap.range f) :=
  LinearEquiv.ofInjective f hinj

theorem rangeEquiv_coe (f : E →ₗ[𝕜] F) (hinj : Function.Injective f) (x : E) :
    ((rangeEquiv f hinj x : ↥(LinearMap.range f)) : F) = f x := rfl

theorem continuous_rangeEquiv (f : E →ₗ[𝕜] F) (hf : Continuous f)
    (hinj : Function.Injective f) : Continuous (rangeEquiv f hinj) := by
  rw [continuous_induced_rng]
  exact hf

/-- **The inverse on a closed range is continuous.** -/
theorem continuous_rangeEquiv_symm_of_isClosed (f : E →ₗ[𝕜] F) (hf : Continuous f)
    (hinj : Function.Injective f) (hclosed : IsClosed (LinearMap.range f : Set F)) :
    Continuous (rangeEquiv f hinj).symm := by
  haveI : CompleteSpace ↥(LinearMap.range f) := hclosed.completeSpace_coe
  haveI : IsUniformAddGroup ↥(LinearMap.range f) :=
    inferInstanceAs (IsUniformAddGroup ↥((LinearMap.range f).toAddSubgroup))
  haveI : TopologicalSpace.PseudoMetrizableSpace ↥(LinearMap.range f) :=
    TopologicalSpace.PseudoMetrizableSpace.subtype (LinearMap.range f : Set F)
  exact continuous_symm_of_continuous _ (continuous_rangeEquiv f hf hinj)

/-- **An injective map with a discontinuous inverse on its range has non-closed range.**  This is
the contrapositive form used to rule out closed range. -/
theorem not_isClosed_range_of_not_continuous_symm (f : E →ₗ[𝕜] F) (hf : Continuous f)
    (hinj : Function.Injective f) (hdisc : ¬ Continuous (rangeEquiv f hinj).symm) :
    ¬ IsClosed (LinearMap.range f : Set F) :=
  fun hclosed => hdisc (continuous_rangeEquiv_symm_of_isClosed f hf hinj hclosed)

end GaloisForLFunctions
