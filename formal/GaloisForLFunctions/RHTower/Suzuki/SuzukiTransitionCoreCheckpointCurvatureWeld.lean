import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreAbelSourceMultiGateWeld
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiGammaBinetCofinalBridge

/-!
# Checkpoint-curvature source for the Suzuki transition core

The completed Abel scalar driving the aligned transition-core carrier admits a second exact
pre-divisor presentation.  Splitting off the first two Selberg cells and using the finite
Suzuki curvature action identifies it with a first moment of literal prime--polar--Gamma cells,
together with the terminal Chebyshev, polar-lattice, and archimedean corrections.

This joins the CCM-FU checkpoint/Gamma complex directly to the SP-E transition core and its
coefficient- and multiplicity-faithful Xi fission.  Every identity is finite and unconditional;
no order is inferred from the signed curvature moment.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Completed transition-core source in signed Suzuki-checkpoint coordinates. -/
def suzukiTransitionCoreCheckpointCurvatureSource (N : ℕ) : ℝ :=
  (suzukiCheckpointWeightedSignedCurvaturePrefix N +
      (Real.sqrt 2 - 1) * psiRemainder 1 +
      (Real.sqrt 3 - Real.sqrt 2) * psiRemainder 2 -
      Real.sqrt 3 * psiRemainder 2 +
      (N + 1 : ℕ) * criticalMellinNormalizedChebyshevError
        (Real.log ((N + 1 : ℕ) : ℝ)) -
      suzukiCheckpointWeightedSelbergArchRemainderPrefix N +
      coherentSquareRootPolarLatticeDefect (N + 1)) / (N + 1 : ℕ) -
    unitRieszSuzukiPolarCorrection (Real.log ((N + 1 : ℕ) : ℝ)) +
    unitRieszSuzukiArchCorrection (Real.log ((N + 1 : ℕ) : ℝ))

/-- Same completed source with every Suzuki curvature cell expanded as its literal
polar-minus-Gamma-minus-prime interval contribution. -/
def suzukiTransitionCorePrimePolarGammaCurvatureSource (N : ℕ) : ℝ :=
  (ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix N +
      (Real.sqrt 2 - 1) * psiRemainder 1 +
      (Real.sqrt 3 - Real.sqrt 2) * psiRemainder 2 -
      Real.sqrt 3 * psiRemainder 2 +
      (N + 1 : ℕ) * criticalMellinNormalizedChebyshevError
        (Real.log ((N + 1 : ℕ) : ℝ)) -
      suzukiCheckpointWeightedSelbergArchRemainderPrefix N +
      coherentSquareRootPolarLatticeDefect (N + 1)) / (N + 1 : ℕ) -
    unitRieszSuzukiPolarCorrection (Real.log ((N + 1 : ℕ) : ℝ)) +
    unitRieszSuzukiArchCorrection (Real.log ((N + 1 : ℕ) : ℝ))

/-- Finite completed-Abel/checkpoint-curvature weld.  The first two Selberg cells and every
terminal correction remain explicit, so no coefficient or endpoint contribution is discarded. -/
theorem suzukiTransitionCoreCompletedAbelSource_succ_eq_checkpointCurvature
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreCompletedAbelSource (N + 1) =
      suzukiTransitionCoreCheckpointCurvatureSource N := by
  rw [suzukiTransitionCoreCompletedAbelSource,
    suzukiTransitionCoreCheckpointCurvatureSource,
    coherentSelbergSquareRootAbelMoment_succ_eq_checkpoint hN,
    weightedSignedCurvature_eq_normalizedErrorBoundary_add_squareRootAbel_arch hN]
  ring

/-- The checkpoint source is coefficient-faithfully the literal prime--polar--Gamma source. -/
theorem suzukiTransitionCoreCheckpointCurvatureSource_eq_primePolarGamma
    (N : ℕ) :
    suzukiTransitionCoreCheckpointCurvatureSource N =
      suzukiTransitionCorePrimePolarGammaCurvatureSource N := by
  rw [suzukiTransitionCoreCheckpointCurvatureSource,
    suzukiTransitionCorePrimePolarGammaCurvatureSource,
    weightedSignedCurvaturePrefix_eq_primePolarGamma]

/-- Direct pre-divisor landing of the transition-core scalar in literal prime--polar--Gamma
coordinates. -/
theorem suzukiTransitionCoreCompletedAbelSource_succ_eq_primePolarGammaCurvature
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreCompletedAbelSource (N + 1) =
      suzukiTransitionCorePrimePolarGammaCurvatureSource N := by
  rw [suzukiTransitionCoreCompletedAbelSource_succ_eq_checkpointCurvature hN,
    suzukiTransitionCoreCheckpointCurvatureSource_eq_primePolarGamma]

/-- The same literal cell source controls the completed growing-rank Gamma energy. -/
theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_primePolarGammaCurvature
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) =
      suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) *
        (suzukiTransitionCorePrimePolarGammaCurvatureSource N /
          unitRieszCoherentPrimeOutgoingCharge (N + 1)) ^ (2 : ℕ) := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy_eq_completedAbelSource
      (by omega : 2 ≤ N + 1) hcharge,
    suzukiTransitionCoreCompletedAbelSource_succ_eq_primePolarGammaCurvature hN]

/-- Multi-gate Xi landing: literal prime--polar--Gamma cells retain transition interaction,
analytic divisor multiplicity, both reflection orientations, and the four-orientation short. -/
theorem
    suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_succ_eq_primePolarGammaCurvature
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0)
    (rho : XiDivisorSupport) (r : ℝ) :
    suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy (N + 1) rho r =
      2 * (xiSupportMultiplicity rho : ℝ) *
        suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) *
          (suzukiTransitionCorePrimePolarGammaCurvatureSource N /
            unitRieszCoherentPrimeOutgoingCharge (N + 1)) ^ (2 : ℕ) *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  rw [suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_eq_completedAbelSource
      (by omega : 2 ≤ N + 1) hcharge,
    suzukiTransitionCoreCompletedAbelSource_succ_eq_primePolarGammaCurvature hN]

end

end GaloisForLFunctions.RHTower
