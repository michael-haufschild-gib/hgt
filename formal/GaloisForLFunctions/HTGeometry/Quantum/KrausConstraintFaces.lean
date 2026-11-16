import GaloisForLFunctions.HTGeometry.Quantum.PositiveConstraintSupport
import GaloisForLFunctions.HTGeometry.FiniteQuantumOperationalMemoryLaw

/-!
# Exact leakage certificates for quantum channels

The output constraint energy of a Kraus channel is a sum of nonnegative branch
energies. It vanishes exactly when every Kraus branch lands in the constraint
kernel. This is the positive-support principle applied to open-system dynamics.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix RHTower

/-- Channel leakage splits into the squared constraints of its individual branches. -/
theorem constraintEnergy_evolveMatrix {d k : ℕ} (Φ : FiniteKrausChannel d k)
    (C ρ : QuantumMatrix d) :
    constraintEnergy C (Φ.evolveMatrix ρ) =
      ∑ a, constraintEnergy (C * Φ.operator a) ρ := by
  simp only [constraintEnergy, FiniteKrausChannel.evolveMatrix, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- An output state has zero leakage iff every Kraus branch obeys the exact constraint. -/
theorem constraintEnergy_evolve_eq_zero_iff {d k : ℕ}
    (Φ : FiniteKrausChannel d k) (C : QuantumMatrix d) (ρ : RHTower.DensityMatrix d) :
    constraintEnergy C (Φ.evolve ρ).1 = 0 ↔
      ∀ a, C * Φ.operator a * ρ.1 = 0 := by
  change constraintEnergy C (Φ.evolveMatrix ρ.1) = 0 ↔ _
  rw [constraintEnergy_evolveMatrix, sum_constraintEnergy_eq_zero_iff _ ρ.2.1]

/-- The full family of output constraints is equivalent to all branchwise kernel equations. -/
theorem evolve_constraintHamiltonian_eq_zero_iff {d k : ℕ}
    {σ : Type*} [Fintype σ] (Φ : FiniteKrausChannel d k)
    (C : σ → QuantumMatrix d) (ρ : RHTower.DensityMatrix d) :
    (constraintHamiltonian C * (Φ.evolve ρ).1).trace.re = 0 ↔
      ∀ s a, C s * Φ.operator a * ρ.1 = 0 := by
  rw [trace_constraintHamiltonian_eq_zero_iff C (Φ.evolve ρ).2.1]
  apply forall_congr'
  intro s
  rw [← constraintEnergy_eq_zero_iff (C s) (Φ.evolve ρ).2.1,
    constraintEnergy_evolve_eq_zero_iff]

end GaloisForLFunctions.HTGeometry.Quantum

#print axioms GaloisForLFunctions.HTGeometry.Quantum.constraintEnergy_evolveMatrix
#print axioms GaloisForLFunctions.HTGeometry.Quantum.constraintEnergy_evolve_eq_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.evolve_constraintHamiltonian_eq_zero_iff
