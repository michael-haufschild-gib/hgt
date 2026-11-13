import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicClosedLimit
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicCutoffRecovery

/-!
# Attainment of the soft logarithmic half-line floor

A compact minimizing sequence gives a unit finite-energy limit below the
trial infimum. Compact trial recovery gives the reverse inequality for
every unit vector in the literal domain, so the infimum is attained there.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- Compact trial recovery extends the variational floor to the literal closed domain. -/
theorem ClosedSoftLogarithmicHalfLineDomain.groundEnergy_le {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) (hn : ‖v‖ = 1) :
    softLogarithmicHalfLineGroundEnergy ≤ closedSoftLogarithmicHalfLineEnergy v := by
  obtain ⟨F, hF, hm, _, he⟩ := exists_softLogarithmic_unit_recovery hv hn
  exact ge_of_tendsto he (Eventually.of_forall fun n =>
    softLogarithmicHalfLineGroundEnergy_le (hF n) (hm n))

/-- Linear confinement and logarithmic Fourier energy attain the unit half-line floor. -/
theorem exists_closedSoftLogarithmic_groundState :
    ∃ v : SoninL2, ClosedSoftLogarithmicHalfLineDomain v ∧ ‖v‖ = 1 ∧
      closedSoftLogarithmicHalfLineEnergy v = softLogarithmicHalfLineGroundEnergy := by
  obtain ⟨v, hv, hn, he⟩ := exists_closedSoftLogarithmic_unit_below_floor
  exact ⟨v, hv, hn, le_antisymm he (hv.groundEnergy_le hn)⟩

#print axioms ClosedSoftLogarithmicHalfLineDomain.groundEnergy_le
#print axioms exists_closedSoftLogarithmic_groundState
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

