import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Repetition.Three
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.Three
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.CSS_4_1_2
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.FiveQubit_5_1_3
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.FourQubit_4_2_2
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.SixQubit_6_2_2
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.Steane7

/-!
# Super-Poincare certificates for concrete stabilizer codes

Every closed logical Pauli anticommutation theorem below becomes an exact matrix representation of
the one-dimensional `N = 2` Super-Poincare supertranslation sector.  Both logical supercharges
square to unit momentum.  The construction uses the actual matrix representation, not only the
binary symplectic shadow.
-/

open Matrix

noncomputable section

namespace Quantum.SuperPoincareApplications

open NQubitPauliGroupElement

/-- A phase-zero Pauli matrix squares to the identity. -/
lemma toMatrix_sq_eq_one_of_phasePower_eq_zero
    {n : ℕ} (p : NQubitPauliGroupElement n) (hp : p.phasePower = 0) :
    p.toMatrix * p.toMatrix = 1 := by
  have hinv : p⁻¹ = p := by
    apply NQubitPauliGroupElement.ext
    · simp [NQubitPauliGroupElement.inv_eq, NQubitPauliGroupElement.inv, hp]
    · rfl
  have hsq : p * p = 1 := by
    simpa only [hinv] using NQubitPauliGroupElement.mul_right_inv p
  calc
    p.toMatrix * p.toMatrix = (p * p).toMatrix :=
      (NQubitPauliGroupElement.toMatrix_mul p p).symm
    _ = 1 := by rw [hsq, NQubitPauliGroupElement.toMatrix_one]

/-- Abstract Pauli anticommutation becomes a zero matrix anticommutator. -/
lemma toMatrix_anticommutator_eq_zero
    {n : ℕ} (p q : NQubitPauliGroupElement n)
    (h : NQubitPauliGroupElement.Anticommute p q) :
    p.toMatrix * q.toMatrix + q.toMatrix * p.toMatrix = 0 := by
  rw [h.toMatrix_mul_neg]
  module

/-- Turn two phase-zero anticommuting Paulis into a unit-momentum `N = 2` certificate. -/
def pauliD1N2
    {n : ℕ} (p q : NQubitPauliGroupElement n)
    (hp : p.phasePower = 0) (hq : q.phasePower = 0)
    (h : NQubitPauliGroupElement.Anticommute p q) :
    SuperPoincare.D1N2 (Matrix (NQubitBasis n) (NQubitBasis n) ℂ) where
  supercharge0 := p.toMatrix
  supercharge1 := q.toMatrix
  momentum := 1
  supercharge0_sq := toMatrix_sq_eq_one_of_phasePower_eq_zero p hp
  supercharge1_sq := toMatrix_sq_eq_one_of_phasePower_eq_zero q hq
  mixed_anticommutator := toMatrix_anticommutator_eq_zero p q h

/-- Three-qubit repetition-code logical supercharges. -/
def repetitionThreeLogical : SuperPoincare.D1N2
    (Matrix (NQubitBasis 3) (NQubitBasis 3) ℂ) :=
  pauliD1N2
    StabilizerGroup.RepetitionCode3.logicalX
    StabilizerGroup.RepetitionCode3.logicalZ rfl rfl
    StabilizerGroup.RepetitionCode3.logicalX_anticommutes_logicalZ

/-- Three-qubit repetition-code local `Z` and logical `X` as supercharges. -/
def repetitionThreeLocalLogical : SuperPoincare.D1N2
    (Matrix (NQubitBasis 3) (NQubitBasis 3) ℂ) :=
  pauliD1N2
    StabilizerGroup.RepetitionCode3.Z_on_qubit2
    StabilizerGroup.RepetitionCode3.logicalX rfl rfl
    StabilizerGroup.RepetitionCode3.Z_on_qubit2_anticommutes_logicalX

/-- Distance-three rotated-surface logical supercharges. -/
def rotatedSurfaceThreeLogical : SuperPoincare.D1N2
    (Matrix (NQubitBasis 9) (NQubitBasis 9) ℂ) :=
  pauliD1N2
    StabilizerGroup.RotatedSurfaceCode3.logicalX
    StabilizerGroup.RotatedSurfaceCode3.logicalZ rfl rfl
    StabilizerGroup.RotatedSurfaceCode3.logicalX_anticommutes_logicalZ

/-- `[[4,1,2]]` CSS logical supercharges. -/
def cssFourLogical : SuperPoincare.D1N2
    (Matrix (NQubitBasis 4) (NQubitBasis 4) ℂ) :=
  pauliD1N2
    StabilizerGroup.CSS_4_1_2.logicalX
    StabilizerGroup.CSS_4_1_2.logicalZ rfl rfl
    StabilizerGroup.CSS_4_1_2.logicalX_anticommutes_logicalZ

/-- Five-qubit perfect-code logical supercharges. -/
def fiveQubitLogical : SuperPoincare.D1N2
    (Matrix (NQubitBasis 5) (NQubitBasis 5) ℂ) :=
  pauliD1N2
    StabilizerGroup.FiveQubit_5_1_3.logicalX
    StabilizerGroup.FiveQubit_5_1_3.logicalZ rfl rfl
    StabilizerGroup.FiveQubit_5_1_3.logicalX_anticommutes_logicalZ

/-- First logical qubit of the `[[4,2,2]]` code. -/
def fourQubitLogical0 : SuperPoincare.D1N2
    (Matrix (NQubitBasis 4) (NQubitBasis 4) ℂ) :=
  pauliD1N2
    StabilizerGroup.FourQubit_4_2_2.logicalX_1
    StabilizerGroup.FourQubit_4_2_2.logicalZ_1 rfl rfl
    StabilizerGroup.FourQubit_4_2_2.logicalX_1_anticommutes_logicalZ_1

/-- Second logical qubit of the `[[4,2,2]]` code. -/
def fourQubitLogical1 : SuperPoincare.D1N2
    (Matrix (NQubitBasis 4) (NQubitBasis 4) ℂ) :=
  pauliD1N2
    StabilizerGroup.FourQubit_4_2_2.logicalX_2
    StabilizerGroup.FourQubit_4_2_2.logicalZ_2 rfl rfl
    StabilizerGroup.FourQubit_4_2_2.logicalX_2_anticommutes_logicalZ_2

/-- First logical qubit of the `[[6,2,2]]` code. -/
def sixQubitLogical0 : SuperPoincare.D1N2
    (Matrix (NQubitBasis 6) (NQubitBasis 6) ℂ) :=
  pauliD1N2
    StabilizerGroup.SixQubit_6_2_2.logicalX_1
    StabilizerGroup.SixQubit_6_2_2.logicalZ_1 rfl rfl
    StabilizerGroup.SixQubit_6_2_2.logicalX_1_anticommutes_logicalZ_1

/-- Second logical qubit of the `[[6,2,2]]` code. -/
def sixQubitLogical1 : SuperPoincare.D1N2
    (Matrix (NQubitBasis 6) (NQubitBasis 6) ℂ) :=
  pauliD1N2
    StabilizerGroup.SixQubit_6_2_2.logicalX_2
    StabilizerGroup.SixQubit_6_2_2.logicalZ_2 rfl rfl
    StabilizerGroup.SixQubit_6_2_2.logicalX_2_anticommutes_logicalZ_2

/-- Steane-code logical supercharges. -/
def steaneLogical : SuperPoincare.D1N2
    (Matrix (NQubitBasis 7) (NQubitBasis 7) ℂ) :=
  pauliD1N2
    StabilizerGroup.Steane7.logicalX
    StabilizerGroup.Steane7.logicalZ rfl rfl
    StabilizerGroup.Steane7.logicalX_anticommutes_logicalZ

end Quantum.SuperPoincareApplications
