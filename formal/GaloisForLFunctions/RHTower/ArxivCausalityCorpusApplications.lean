import GaloisForLFunctions.HTGeometry.Arxiv2608CausalitySumRules
import GaloisForLFunctions.HTGeometry.Arxiv2607CausalInteractionSelection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalSchwarzSupport
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGaugeFixedCausalQNMCokernel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEKGCausalMirrorOpticalLaw
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeForcedIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOnsetGreenReconstruction

/-!
# Causality-paper applications in RHTower

The exact interaction-shell theorem of arXiv:2607.29504 is instantiated on the
corpus's concrete BM retarded/advanced modes, native radial response, EKG memory,
and onset Green reconstruction.  The one-channel delay theorem of arXiv:2608.10427
is also applied to concrete scalar causal responses.  These are exact finite-batch
identities, not numerical approximations.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open D4BMNativeResponse D4BMOnsetGreenReconstruction

theorem d4BMRetardedTimeMode_exactCausalBatchPruning
    (batch : Finset ℤ) (logStep tₐ tᵦ τ : ℝ) (omega : ℂ) :
    causalBatchResponse batch logStep tₐ tᵦ τ
        (fun k => d4BMRetardedTimeMode omega
          ((k : ℝ) * Real.exp logStep - τ)) =
      causalPrunedBatchResponse batch logStep tₐ tᵦ τ
        (fun k => d4BMRetardedTimeMode omega
          ((k : ℝ) * Real.exp logStep - τ)) :=
  causalBatchResponse_eq_causalPrunedBatchResponse _ _ _ _ _ _

theorem d4BMAdvancedTimeMode_exactCausalBatchPruning
    (batch : Finset ℤ) (logStep tₐ tᵦ τ : ℝ) (omega : ℂ) :
    causalBatchResponse batch logStep tₐ tᵦ τ
        (fun k => d4BMAdvancedTimeMode omega
          ((k : ℝ) * Real.exp logStep - τ)) =
      causalPrunedBatchResponse batch logStep tₐ tᵦ τ
        (fun k => d4BMAdvancedTimeMode omega
          ((k : ℝ) * Real.exp logStep - τ)) :=
  causalBatchResponse_eq_causalPrunedBatchResponse _ _ _ _ _ _

theorem radialResponse_exactCausalBatchPruning
    (batch : Finset ℤ) (logStep tₐ tᵦ τ : ℝ)
    (nu s a : ℂ) (x : ℝ) :
    causalBatchResponse batch logStep tₐ tᵦ τ
        (fun k => radialResponse nu s a
          ((k : ℝ) * Real.exp logStep - τ) x) =
      causalPrunedBatchResponse batch logStep tₐ tᵦ τ
        (fun k => radialResponse nu s a
          ((k : ℝ) * Real.exp logStep - τ) x) :=
  causalBatchResponse_eq_causalPrunedBatchResponse _ _ _ _ _ _

theorem radialResponseVector_exactCausalBatchPruning
    (batch : Finset ℤ) (logStep tₐ tᵦ τ : ℝ) (nu s a : ℂ) :
    causalBatchResponse batch logStep tₐ tᵦ τ
        (fun k => radialResponseVector nu s a
          ((k : ℝ) * Real.exp logStep - τ)) =
      causalPrunedBatchResponse batch logStep tₐ tᵦ τ
        (fun k => radialResponseVector nu s a
          ((k : ℝ) * Real.exp logStep - τ)) :=
  causalBatchResponse_eq_causalPrunedBatchResponse _ _ _ _ _ _

theorem thetaCuspTiltedEKGRetardedDerivativeEnergy_exactCausalBatchPruning
    (batch : Finset ℤ) (logStep tₐ tᵦ τ a : ℝ) :
    causalBatchResponse batch logStep tₐ tᵦ τ
        (fun k => thetaCuspTiltedEKGRetardedDerivativeEnergy a
          ((k : ℝ) * Real.exp logStep - τ)) =
      causalPrunedBatchResponse batch logStep tₐ tᵦ τ
        (fun k => thetaCuspTiltedEKGRetardedDerivativeEnergy a
          ((k : ℝ) * Real.exp logStep - τ)) :=
  causalBatchResponse_eq_causalPrunedBatchResponse _ _ _ _ _ _

theorem thetaCuspTiltedEKGAdvancedDerivativeEnergy_exactCausalBatchPruning
    (batch : Finset ℤ) (logStep tₐ tᵦ τ a : ℝ) :
    causalBatchResponse batch logStep tₐ tᵦ τ
        (fun k => thetaCuspTiltedEKGAdvancedDerivativeEnergy a
          ((k : ℝ) * Real.exp logStep - τ)) =
      causalPrunedBatchResponse batch logStep tₐ tᵦ τ
        (fun k => thetaCuspTiltedEKGAdvancedDerivativeEnergy a
          ((k : ℝ) * Real.exp logStep - τ)) :=
  causalBatchResponse_eq_causalPrunedBatchResponse _ _ _ _ _ _

theorem retardedNullAction_exactCausalBatchPruning
    (batch : Finset ℤ) (logStep tₐ tᵦ τ : ℝ)
    (S : ℝ → ℝ → D4BMHorizon.Point → ℂ) (p width : NNReal) (X : ℝ) :
    causalBatchResponse batch logStep tₐ tᵦ τ
        (fun k => retardedNullAction S p width X
          ((k : ℝ) * Real.exp logStep - τ)) =
      causalPrunedBatchResponse batch logStep tₐ tᵦ τ
        (fun k => retardedNullAction S p width X
          ((k : ℝ) * Real.exp logStep - τ)) :=
  causalBatchResponse_eq_causalPrunedBatchResponse _ _ _ _ _ _

theorem d4BMCausalRetardedTurnOnMultiplier_domainDelay_norm
    (omega tau : ℝ) (target source : ℂ) :
    ‖causalityDomainDelayPhase omega tau *
        d4BMCausalRetardedTurnOnMultiplier target source‖ =
      ‖d4BMCausalRetardedTurnOnMultiplier target source‖ :=
  norm_causalityDomainDelayPhase_mul _ _ _

theorem d4BMRetardedTimeMode_domainDelay_norm
    (omega tau t : ℝ) (frequency : ℂ) :
    ‖causalityDomainDelayPhase omega tau * d4BMRetardedTimeMode frequency t‖ =
      ‖d4BMRetardedTimeMode frequency t‖ :=
  norm_causalityDomainDelayPhase_mul _ _ _

theorem radialResponse_domainDelay_norm
    (omega tau : ℝ) (nu s a : ℂ) (time x : ℝ) :
    ‖causalityDomainDelayPhase omega tau * radialResponse nu s a time x‖ =
      ‖radialResponse nu s a time x‖ :=
  norm_causalityDomainDelayPhase_mul _ _ _

theorem retardedNullAction_domainDelay_norm
    (omega tau : ℝ) (S : ℝ → ℝ → D4BMHorizon.Point → ℂ)
    (p width : NNReal) (X k : ℝ) :
    ‖causalityDomainDelayPhase omega tau * retardedNullAction S p width X k‖ =
      ‖retardedNullAction S p width X k‖ :=
  norm_causalityDomainDelayPhase_mul _ _ _

end


end RHTower
