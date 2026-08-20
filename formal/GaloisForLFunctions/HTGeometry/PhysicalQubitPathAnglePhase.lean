/-
# The joint angular-phase law on the card's ensemble

Feeding the recursive physical qubit path's own dephasing theorem into the base-times-character
reduction gives the card's `(16)` on that ensemble with no hypotheses beyond the choice of a base
spectral label: the joint law of a coefficient direction and its rescaled projective phase vector
converges weakly to the product of the fixed-shell law with Haar measure on the phase torus.

Main results:
* `physicalStateBool_card_pos` — the spectral label set is nonempty.
* `tendsto_integral_anglePhase_physicalQubitPath` — **`(16)` on the card's ensemble**.
-/
import GaloisForLFunctions.HTGeometry.AngularPhaseLaw
import GaloisForLFunctions.HTGeometry.PhysicalQubitPathDephasing

open Filter Topology MeasureTheory Metric

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem physicalStateBool_card_pos (Z : PhysicallyRealizedEndpointCompleteSystem) :
    0 < Fintype.card (Z.PhysicalState × Bool) := by
  rw [Fintype.card_prod]
  have h1 : 0 < Fintype.card Z.PhysicalState := by
    rw [Z.physicalCard_eq_stateCard]
    exact lt_of_lt_of_le (by norm_num) Z.three_le_stateCard
  have h2 : 0 < Fintype.card Bool := by norm_num
  exact Nat.mul_pos h1 h2

/-- **`(16)` on the card's ensemble.**  The joint angular-phase laws of the recursive physical
qubit path converge weakly to the product of the fixed-shell law with Haar measure on the phase
torus. -/
theorem tendsto_integral_anglePhase_physicalQubitPath (n : ℕ)
    (i₀ : Fin (Fintype.card ((physicalEndpointCompleteQubitPath n).PhysicalState × Bool)))
    (F : C(coeffSphere ((physicalEndpointCompleteQubitPath n).leafLocalParameterCount)
      × UnitAddTorus (phaseIndex i₀), ℂ)) :
    Tendsto (fun t : ℝ =>
        ∫ x, F (anglePhaseMap
          (physicalEndpointCompleteQubitPath n).leafLocalTraceGeneratorFin_isHermitian i₀ t x)
        ∂(sphereLaw ((physicalEndpointCompleteQubitPath n).leafLocalParameterCount))) atTop
      (nhds (∫ y, F y
        ∂((sphereLaw ((physicalEndpointCompleteQubitPath n).leafLocalParameterCount)).prod
          volume))) := by
  refine tendsto_integral_anglePhase
    (physicalEndpointCompleteQubitPath n).leafLocalParameterCount_pos
    (physicalEndpointCompleteQubitPath n).leafLocalTraceGeneratorFin_isHermitian i₀ ?_ F
  intro a hsum hane g hg C hC0 hC
  exact tendsto_integral_exp_sortedSpectralAction_zero_physicalQubitPath n a hsum hane g hg hC0 hC

/-- A base spectral label exists. -/
def physicalBaseLabel (n : ℕ) :
    Fin (Fintype.card ((physicalEndpointCompleteQubitPath n).PhysicalState × Bool)) :=
  ⟨0, physicalStateBool_card_pos _⟩

end

end GaloisForLFunctions.HTGeometry
