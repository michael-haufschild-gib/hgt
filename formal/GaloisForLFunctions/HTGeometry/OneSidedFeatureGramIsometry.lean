import GaloisForLFunctions.HTGeometry.DenseFeatureGramUnitary

/-!
# A one-sided feature-Gram isometry

Two feature families with the same Gram kernel determine an isometry between their algebraic
spans.  If only the first family is total, completion still gives a canonical isometry from the
whole first Hilbert space into the second one; no density or surjectivity is required on the target
family.  Its range is the closed span of the target features.
-/

open scoped InnerProductSpace
open Set UniformSpace Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The canonical isometry induced by equal Gram kernels when the source feature family is total.
The target range is allowed to be a proper closed subspace. -/
noncomputable def denseSourceFeatureGramIsometry
    (v : ι → H) (w : ι → K)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (hdenseV : Dense ((LinearMap.range (featureSynthesis v) :
      Submodule ℂ H) : Set H)) : H →ₗᵢ[ℂ] K :=
  (completionExtendₗᵢ (rightFeatureRangeInclusion v w hgram)).comp
    (completionLinearIsometryEquivOfDenseRange
      (leftFeatureRangeInclusion v)
      (denseRange_leftFeatureRangeInclusion v hdenseV)).symm.toLinearIsometry

/-- The one-sided Gram isometry carries every named source feature to its target counterpart. -/
theorem denseSourceFeatureGramIsometry_apply
    (v : ι → H) (w : ι → K)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (hdenseV : Dense ((LinearMap.range (featureSynthesis v) :
      Submodule ℂ H) : Set H)) (i : ι) :
    denseSourceFeatureGramIsometry v w hgram hdenseV (v i) = w i := by
  let rv : LinearMap.range (featureSynthesis v) :=
    ⟨v i, ⟨Finsupp.single i 1, by simp⟩⟩
  let UL := completionLinearIsometryEquivOfDenseRange
    (leftFeatureRangeInclusion v)
    (denseRange_leftFeatureRangeInclusion v hdenseV)
  have hUL : UL (rv : Completion (LinearMap.range (featureSynthesis v))) = v i := by
    dsimp only [UL]
    rw [completionLinearIsometryEquivOfDenseRange_coe]
    rfl
  have hULsymm : UL.symm (v i) =
      (rv : Completion (LinearMap.range (featureSynthesis v))) := by
    apply UL.injective
    rw [UL.apply_symm_apply]
    exact hUL.symm
  change completionExtendₗᵢ (rightFeatureRangeInclusion v w hgram)
      (UL.symm (v i)) = w i
  rw [hULsymm, completionExtendₗᵢ_coe]
  exact featureRangeGramEquiv_single v w hgram i

end GaloisForLFunctions.HTGeometry
