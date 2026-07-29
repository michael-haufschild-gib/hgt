import GaloisForLFunctions.HTGeometry.FiniteClockUnitaryReferenceFrameMasterObservabilityUniversalityLaw
import GaloisForLFunctions.RHTower.SoninLogPinchingProjectiveRayUniversalityLaw

/-!
# Sonin-pinching unitary-frame projective-ray universality

The native Sonin pinching zero locus survives arbitrary two-sided unitary reference-frame change:
the observed vector remains physical for the conjugated scattering constraint and its projective
Gram energy remains exactly zero.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Two-vector projective Gram energy is invariant under an adjoint-isometric frame map. -/
private theorem projectiveGramTangentEnergy_unitaryReferenceFrame
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (V : E →L[𝕜] E) (v w : E) (hleft : V.adjoint * V = 1) :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := 𝕜) (V v) (V w) =
      HTGeometry.projectiveGramTangentEnergy (𝕜 := 𝕜) v w := by
  have hvSq :
      ‖V v‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa using
      (HTGeometry.norm_pow_apply_sq_eq_of_adjoint_mul_self V 1 hleft v)
  have hwSq :
      ‖V w‖ ^ 2 = ‖w‖ ^ 2 := by
    simpa using
      (HTGeometry.norm_pow_apply_sq_eq_of_adjoint_mul_self V 1 hleft w)
  have hinner :
      inner 𝕜 (V v) (V w) = inner 𝕜 v w := by
    rw [← V.adjoint_inner_left w (V v)]
    have hleftApply := congrArg (fun T : E →L[𝕜] E => T v) hleft
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using
      congrArg (fun y : E => inner 𝕜 y w) hleftApply
  unfold HTGeometry.projectiveGramTangentEnergy
  rw [hvSq, hwSq, hinner]

/-- **Sonin-pinching unitary-frame projective-ray universality law.** -/
theorem soninLogPinching_unitaryFrameProjectiveRayUniversality
    (X V : SoninL2 →L[ℂ] SoninL2)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ)
    (hleft : V.adjoint * V = 1) (hright : V * V.adjoint = 1) :
    let Y := HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X
    GaloisForLFunctions.PhysicalState
        (V * soninLogFourierScattering * V.adjoint - 1).toLinearMap
        (V (Y ψ)) ∧
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (V (Y ψ))
          ((V * soninLogFourierScattering * V.adjoint) (V (Y ψ))) =
        HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (Y ψ)
          (soninLogFourierScattering (Y ψ)) ∧
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (V (Y ψ))
          ((V * soninLogFourierScattering * V.adjoint) (V (Y ψ))) = 0 := by
  dsimp only
  let Y := HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X
  have hnative := soninLogPinching_projectiveRayUniversality X hψnorm hψ
  have hphysicalNative :
      GaloisForLFunctions.PhysicalState
        (soninLogFourierScattering - 1).toLinearMap (Y ψ) :=
    hnative.2.1
  have hprojectiveNative :
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (Y ψ)
        (soninLogFourierScattering (Y ψ)) = 0 :=
    hnative.2.2.2
  have hphysicalFrame :
      GaloisForLFunctions.PhysicalState
        (V * (soninLogFourierScattering - 1) * V.adjoint).toLinearMap
        (V (Y ψ)) :=
    (HTGeometry.physicalState_twoSidedConjugation_iff
      (soninLogFourierScattering - 1) V V.adjoint (Y ψ) hleft).2
      hphysicalNative
  rw [← HTGeometry.twoSidedConjugation_sub_one
    soninLogFourierScattering V V.adjoint hright] at hphysicalFrame
  have hscatter :
      (V * soninLogFourierScattering * V.adjoint) (V (Y ψ)) =
        V (soninLogFourierScattering (Y ψ)) := by
    simp only [mul_apply_eq_comp]
    have hleftApply :=
      congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T (Y ψ)) hleft
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using
      congrArg V (congrArg soninLogFourierScattering hleftApply)
  have hprojectiveFrame :
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (V (Y ψ))
          ((V * soninLogFourierScattering * V.adjoint) (V (Y ψ))) =
        HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (Y ψ)
          (soninLogFourierScattering (Y ψ)) := by
    rw [hscatter]
    exact projectiveGramTangentEnergy_unitaryReferenceFrame
      V (Y ψ) (soninLogFourierScattering (Y ψ)) hleft
  exact
    ⟨hphysicalFrame, hprojectiveFrame,
      hprojectiveFrame.trans hprojectiveNative⟩

end

end RHTower
