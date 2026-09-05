import GaloisForLFunctions.HTGeometry.SpinTorsionCorrelator
import GaloisForLFunctions.HTGeometry.SpinTorsionSectorArithmetic

/-!
# From flux index to spin-torsion dynamics

The compactification index maps integer fluxes to chiral-family multiplicity, while the separated
correlator and radion term depend quadratically on that multiplicity.  Composing those two maps
makes the `n = 5` branch exactly nine times the `n = 3` branch at fixed first flux.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Radion binding term with family multiplicity supplied by the flux index. -/
def fluxIndexedTorsionRadionTerm (C : ℝ) (m n : ℕ) (a1 a2 : ℝ) : ℝ :=
  spinTorsionRadionTerm C (familyCount m n : ℝ) a1 a2

/-- On the `n = 3` branch, the first flux is the family coordinate. -/
theorem fluxIndexedTorsionRadionTerm_three (C : ℝ) (m : ℕ) (a1 a2 : ℝ) :
    fluxIndexedTorsionRadionTerm C m 3 a1 a2 =
      spinTorsionRadionTerm C (m : ℝ) a1 a2 := by
  simp [fluxIndexedTorsionRadionTerm, familyCount_three]

/-- On the `n = 5` branch, family multiplicity triples. -/
theorem fluxIndexedTorsionRadionTerm_five (C : ℝ) (m : ℕ) (a1 a2 : ℝ) :
    fluxIndexedTorsionRadionTerm C m 5 a1 a2 =
      spinTorsionRadionTerm C (3 * (m : ℝ)) a1 a2 := by
  simp [fluxIndexedTorsionRadionTerm, familyCount_five]

/-- Quadratic family binding makes the `n = 5` radion term nine times the `n = 3` term. -/
theorem fluxIndexedTorsionRadionTerm_five_eq_nine_mul_three
    (C : ℝ) (m : ℕ) (a1 a2 : ℝ) :
    fluxIndexedTorsionRadionTerm C m 5 a1 a2 =
      9 * fluxIndexedTorsionRadionTerm C m 3 a1 a2 := by
  rw [fluxIndexedTorsionRadionTerm_five, fluxIndexedTorsionRadionTerm_three]
  unfold spinTorsionRadionTerm
  ring

/-- Separated correlator with family multiplicity supplied by the flux index. -/
def fluxIndexedVacuumSpinTorsionCorrelator
    (dR : ℝ) (m n : ℕ) (volume separation : ℝ) : ℝ :=
  vacuumSpinTorsionCorrelator dR (familyCount m n : ℝ) volume separation

/-- The same index composition amplifies the separated `n = 5` correlator by exactly nine. -/
theorem fluxIndexedVacuumSpinTorsionCorrelator_five_eq_nine_mul_three
    (dR : ℝ) (m : ℕ) (volume separation : ℝ) :
    fluxIndexedVacuumSpinTorsionCorrelator dR m 5 volume separation =
      9 * fluxIndexedVacuumSpinTorsionCorrelator dR m 3 volume separation := by
  unfold fluxIndexedVacuumSpinTorsionCorrelator
  rw [familyCount_five, familyCount_three]
  norm_num
  unfold vacuumSpinTorsionCorrelator
  ring

/-- The exact Hamiltonian coefficient preserves the same ninefold topological amplification. -/
theorem fluxIndexedSeparatedEnergyDensity_five_eq_nine_mul_three
    (logKappa dR : ℝ) (m : ℕ) (volume separation : ℝ) :
    separatedSpinTorsionEnergyDensity logKappa dR (familyCount m 5 : ℝ)
        volume separation =
      9 * separatedSpinTorsionEnergyDensity logKappa dR (familyCount m 3 : ℝ)
        volume separation := by
  unfold separatedSpinTorsionEnergyDensity spinTorsionInteractionHamiltonian
  rw [familyCount_five, familyCount_three]
  norm_num
  unfold vacuumSpinTorsionCorrelator
  ring

end GaloisForLFunctions.HTGeometry
