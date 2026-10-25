import GaloisForLFunctions.ArithmeticDefectRigidity.EnergyQuantilesRetainDiffuseEscape

/-!
# Receiver energy crossings have unit overshoot

The actual receiver energy increases by at most one per cell. On escape,
every positive level has a first crossing whose excess is at most one.
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Every positive energy level on escape has a horizon with overshoot at most one. -/
theorem admits_or_every_positive_level_has_unit_overshoot (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ R : ℝ, 0 < R → ∃ T : ℕ,
        R ≤ dampedMobiusEnergy ε T ∧ dampedMobiusEnergy ε T < R + 1 := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with hpaid | hE
  · exact Or.inl hpaid
  · refine Or.inr fun R hR => ?_
    have hex : ∃ T : ℕ, R ≤ dampedMobiusEnergy ε T := (hE.eventually_ge_atTop R).exists
    let T := Nat.find hex
    have hRT : R ≤ dampedMobiusEnergy ε T := Nat.find_spec hex
    have hTpos : 0 < T := by
      by_contra h
      have hT : T = 0 := by omega
      rw [hT] at hRT
      rw [receiverEnergy_zero] at hRT
      exact hR.not_ge hRT
    have hprev : dampedMobiusEnergy ε (T - 1) < R :=
      lt_of_not_ge (Nat.find_min hex (by omega : T - 1 < T))
    refine ⟨T, hRT, ?_⟩
    have hinc := receiverEnergy_succ_le ε (T - 1)
    rw [Nat.sub_add_cancel hTpos] at hinc
    linarith only [hinc, hprev]

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_every_positive_level_has_unit_overshoot
end
end
