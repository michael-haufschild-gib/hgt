import GaloisForLFunctions.HTGeometry.ScaleInnovationHistoryBundle
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCompletedFormationEnergy

/-!
# Suzuki completed formation innovation history

The completed Suzuki scale potential is lifted to its unique anchored formation history.  The
literal completed Abel source is exactly the next orthogonal innovation of this divisor-free
history, completed formation action is its variance, and aligned Gamma energy is a conditioned
readout of one-step innovation energy.  Eventual bounded innovation birth is exactly RH; the module
does not prove that bound.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unique completed formation history reconstructed from the literal Suzuki potential. -/
def suzukiCompletedFormationInnovationHistory : ℕ → ℝ :=
  completedScaleInnovationHistory suzukiCheckpointAffineSlope
    suzukiTransitionCoreCesaroTerminalCorrection

/-- Weighted squared norm of the next completed Suzuki history innovation. -/
def suzukiCompletedFormationInnovationEnergy (N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) *
    (anchoredCesaroHighPass suzukiCompletedFormationInnovationHistory N) ^ (2 : ℕ)

/-- Scalar projection of completed innovation history is the completed formation potential. -/
theorem suzukiCompletedFormationInnovationHistory_potential
    {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroPotential suzukiCompletedFormationInnovationHistory N =
      suzukiCompletedFormationPotential N := by
  exact anchoredCesaroPotential_completedScaleInnovationHistory
    suzukiCheckpointAffineSlope suzukiTransitionCoreCesaroTerminalCorrection hN

/-- Completed Abel source is exactly the current innovation coordinate of the lifted history. -/
theorem suzukiCompletedFormationInnovationHistory_current
    {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroHighPass suzukiCompletedFormationInnovationHistory N =
      suzukiTransitionCoreCompletedAbelSource (N + 1) := by
  rw [suzukiCompletedFormationInnovationHistory,
    anchoredCesaroHighPass_completedScaleInnovationHistory _ _ hN]
  have hsource := suzukiTransitionCoreCompletedAbelSource_succ_eq_scaleConnection hN
  rw [anchoredCesaroHighPass_eq_scaled_potentialIncrement _ hN]
  unfold suzukiCheckpointAffineSlopeCesaroPotential at hsource
  linarith

/-- Completed formation action is exactly variance of the lifted history. -/
theorem suzukiCompletedFormationInnovationHistory_variance
    {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance suzukiCompletedFormationInnovationHistory N =
      suzukiCompletedFormationEnergy N := by
  exact anchoredCesaroVariance_completedScaleInnovationHistory
    suzukiCheckpointAffineSlope suzukiTransitionCoreCesaroTerminalCorrection hN

/-- Innovation energy is exact one-step production of completed formation action. -/
theorem suzukiCompletedFormationInnovationEnergy_eq_energyProduction
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCompletedFormationInnovationEnergy N =
      suzukiCompletedFormationEnergy (N + 1) -
        suzukiCompletedFormationEnergy N := by
  rw [suzukiCompletedFormationInnovationEnergy,
    suzukiCompletedFormationInnovationHistory_current hN,
    suzukiCompletedFormationEnergy_succ_sub hN]

/-- Aligned Gamma energy is the conditioned readout of one-step innovation energy. -/
theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_innovationEnergy
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) =
      (suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) /
          unitRieszCoherentPrimeOutgoingCharge (N + 1) ^ (2 : ℕ)) *
        (((N + 2 : ℕ) : ℝ) / (N + 1 : ℕ)) *
        suzukiCompletedFormationInnovationEnergy N := by
  rw [suzukiCompletedFormationInnovationEnergy_eq_energyProduction hN]
  exact suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_formationProduction
    hN hcharge

/-- Eventual uniform boundedness of completed Suzuki innovation birth energy. -/
def SuzukiCompletedFormationInnovationEventuallyBounded : Prop :=
  ∃ B : ℝ, ∀ᶠ N : ℕ in atTop,
    suzukiCompletedFormationInnovationEnergy N ≤ B

/-- Bounded innovation birth and bounded completed-action production are identical conditions. -/
theorem suzukiCompletedFormationInnovationEventuallyBounded_iff_energyIncrement :
    SuzukiCompletedFormationInnovationEventuallyBounded ↔
      SuzukiCompletedFormationEnergyIncrementEventuallyBounded := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    filter_upwards [hB, eventually_ge_atTop (2 : ℕ)] with N hbound hN
    rwa [← suzukiCompletedFormationInnovationEnergy_eq_energyProduction hN]
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    filter_upwards [hB, eventually_ge_atTop (2 : ℕ)] with N hbound hN
    rwa [suzukiCompletedFormationInnovationEnergy_eq_energyProduction hN]

/-- Exact innovation-history selection coordinate: RH iff innovation birth is eventually bounded. -/
theorem riemannHypothesis_iff_suzukiCompletedFormationInnovationEventuallyBounded :
    RiemannHypothesis ↔ SuzukiCompletedFormationInnovationEventuallyBounded :=
  riemannHypothesis_iff_suzukiCompletedFormationEnergyIncrementEventuallyBounded.trans
    suzukiCompletedFormationInnovationEventuallyBounded_iff_energyIncrement.symm

end

end GaloisForLFunctions.RHTower
