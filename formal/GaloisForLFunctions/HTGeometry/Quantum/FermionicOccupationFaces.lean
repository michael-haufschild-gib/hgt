import GaloisForLFunctions.HTGeometry.Quantum.PositiveConstraintSupport
import GaloisForLFunctions.HTGeometry.JordanWignerSpinFermionBridge

/-!
# Single-occupation faces of the concrete fermionic chain

Pair the two halves of a `2n`-mode Jordan--Wigner chain into `n` sites. The
sum of their squared occupation defects exposes exactly the states with one
fermion at every site. All contracted occupation identities follow from that
single scalar equality. No occupation or representability premise is assumed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix
open scoped ComplexOrder

/-- The two-orbital site occupation, using disjoint halves of the fermionic chain. -/
def pairedSiteOccupation {n : ℕ} (s : Fin n) :
    Matrix (Fin (2 ^ (n + n))) (Fin (2 ^ (n + n))) ℂ :=
  jordanWignerNumber (s.castAdd n) + jordanWignerNumber (s.natAdd n)

/-- Departure from exactly one fermion on a site. -/
def pairedSiteDefect {n : ℕ} (s : Fin n) :
    Matrix (Fin (2 ^ (n + n))) (Fin (2 ^ (n + n))) ℂ :=
  pairedSiteOccupation s - 1

/-- The occupation defect is half the sum of the two Pauli-Z observables. -/
theorem pairedSiteDefect_eq_pauliZ {n : ℕ} (s : Fin n) :
    pairedSiteDefect s = (2 : ℂ)⁻¹ •
      (QuantumAlg.pauliMat (QuantumAlg.TFIM.zLabel (s.castAdd n)) +
        QuantumAlg.pauliMat (QuantumAlg.TFIM.zLabel (s.natAdd n))) := by
  simp only [pairedSiteDefect, pairedSiteOccupation,
    jordanWignerNumber_eq_half_one_add_pauliZ]
  module

/-- The literal total site-occupation variance operator. -/
def pairedOccupationHamiltonian (n : ℕ) :
    Matrix (Fin (2 ^ (n + n))) (Fin (2 ^ (n + n))) ℂ :=
  constraintHamiltonian (@pairedSiteDefect n)

theorem pairedOccupationHamiltonian_posSemidef (n : ℕ) :
    (pairedOccupationHamiltonian n).PosSemidef :=
  constraintHamiltonian_posSemidef _

/-- Zero occupation-variance expectation is equivalent to exact single occupation at every site. -/
theorem pairedOccupation_zero_iff {n : ℕ}
    {ρ : Matrix (Fin (2 ^ (n + n))) (Fin (2 ^ (n + n))) ℂ} (hρ : ρ.PosSemidef) :
    (pairedOccupationHamiltonian n * ρ).trace.re = 0 ↔
      ∀ s, pairedSiteOccupation s * ρ = ρ := by
  rw [pairedOccupationHamiltonian, trace_constraintHamiltonian_eq_zero_iff _ hρ]
  simp only [pairedSiteDefect, sub_mul, one_mul, sub_eq_zero]

/-- The same scalar variance equality enforces every contracted occupation equation. -/
theorem pairedOccupation_zero_iff_contracted {n : ℕ}
    {ρ : Matrix (Fin (2 ^ (n + n))) (Fin (2 ^ (n + n))) ℂ} (hρ : ρ.PosSemidef) :
    (pairedOccupationHamiltonian n * ρ).trace.re = 0 ↔
      ∀ s A, A * pairedSiteDefect s * ρ = 0 := by
  rw [pairedOccupationHamiltonian, trace_constraintHamiltonian_eq_zero_iff _ hρ]
  apply forall_congr'
  intro s
  rw [← constraintEnergy_eq_zero_iff _ hρ,
    constraintEnergy_eq_zero_iff_all_contractions _ hρ]

/-- The concrete single-occupation fermionic states are an exposed face of all density matrices. -/
theorem pairedOccupation_isExposed (n : ℕ) :
    IsExposed ℝ
      {ρ : Matrix (Fin (2 ^ (n + n))) (Fin (2 ^ (n + n))) ℂ |
        ρ.trace = 1 ∧ ρ.PosSemidef}
      (constraintFace (@pairedSiteDefect n) {ρ | ρ.trace = 1}) :=
  constraintFace_isExposed _ _

end GaloisForLFunctions.HTGeometry.Quantum

#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedSiteDefect_eq_pauliZ
#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedOccupationHamiltonian_posSemidef
#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedOccupation_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedOccupation_zero_iff_contracted
#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedOccupation_isExposed
