import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Repetition.Three
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Repetition.N
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Iceberg.N
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.Three
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.StabilizerCode
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.CSS_4_1_2
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.FiveQubit_5_1_3
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.FourQubit_4_2_2
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.SixQubit_6_2_2
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.Steane7
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.QuantumHamming

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

/-- Every anticommuting Pauli pair gives split `N = 2`, without a phase convention. -/
def pauliD1N2Split
    {n : ℕ} (p q : NQubitPauliGroupElement n)
    (h : NQubitPauliGroupElement.Anticommute p q) :
    SuperPoincare.D1N2Split (Matrix (NQubitBasis n) (NQubitBasis n) ℂ) where
  supercharge0 := p.toMatrix
  supercharge1 := q.toMatrix
  mixed_anticommutator := toMatrix_anticommutator_eq_zero p q h

/-- Every packaged logical qubit canonically carries split `N = 2` supertranslations. -/
def logicalQubitD1N2Split {n : ℕ} {S : Quantum.StabilizerGroup n}
    (ops : Quantum.StabilizerGroup.LogicalQubitOps n S) :
    SuperPoincare.D1N2Split (Matrix (NQubitBasis n) (NQubitBasis n) ℂ) :=
  pauliD1N2Split ops.xOp ops.zOp ops.anticommute

/-- Every encoded qubit of every corpus `StabilizerCode` inherits the construction. -/
def stabilizerCodeLogicalD1N2Split {n k : ℕ}
    (C : Quantum.StabilizerGroup.StabilizerCode n k) (i : Fin k) :
    SuperPoincare.D1N2Split (Matrix (NQubitBasis n) (NQubitBasis n) ℂ) :=
  logicalQubitD1N2Split (C.logicalOps i)

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

/-- Logical supercharges for every odd-length repetition code. -/
def oddRepetitionLogical (k : ℕ) : SuperPoincare.D1N2
    (Matrix (NQubitBasis ((2 * k + 1) + 2)) (NQubitBasis ((2 * k + 1) + 2)) ℂ) :=
  pauliD1N2
    (StabilizerGroup.RepetitionCodeN.logicalX (2 * k + 1))
    (StabilizerGroup.RepetitionCodeN.logicalZ (2 * k + 1)) rfl rfl
    (StabilizerGroup.RepetitionCodeN.logicalX_anticommutes_logicalZ
      (2 * k + 1) ⟨k + 1, by omega⟩)

/-- Logical supercharges for every quantum Hamming code in the corpus. -/
def quantumHammingLogical (k : ℕ) : SuperPoincare.D1N2
    (Matrix (NQubitBasis (2 ^ (k + 1) - 1)) (NQubitBasis (2 ^ (k + 1) - 1)) ℂ) :=
  pauliD1N2
    (StabilizerGroup.QuantumHamming.logicalX (k + 1))
    (StabilizerGroup.QuantumHamming.logicalZ (k + 1)) rfl rfl
    (StabilizerGroup.QuantumHamming.logicalX_anticommutes_logicalZ
      (r := k + 1) (by omega))

/-- Every encoded qubit in every Iceberg code supplies its own `N = 2` representation. -/
def icebergLogical (k : ℕ) (i : Fin (2 * (k + 2) - 2)) : SuperPoincare.D1N2
    (Matrix (NQubitBasis (2 * (k + 2))) (NQubitBasis (2 * (k + 2))) ℂ) := by
  letI : Fact (2 ≤ k + 2) := ⟨by omega⟩
  exact pauliD1N2
    (StabilizerGroup.Iceberg.logicalX (k + 2) i)
    (StabilizerGroup.Iceberg.logicalZ (k + 2) i) rfl rfl
    (StabilizerGroup.Iceberg.logicalX_anticommutes_logicalZ_diag (k + 2) i)

/-- Logical supercharges for every odd rotated-surface lattice of side at least three. -/
def oddRotatedSurfaceLogical (k : ℕ) : SuperPoincare.D1N2
    (Matrix (NQubitBasis ((2 * k + 3) * (2 * k + 3)))
      (NQubitBasis ((2 * k + 3) * (2 * k + 3))) ℂ) := by
  letI : Fact (Odd (2 * k + 3)) := ⟨⟨k + 1, by omega⟩⟩
  letI : Fact (3 ≤ 2 * k + 3) := ⟨by omega⟩
  exact pauliD1N2
    (StabilizerGroup.RotatedSurfaceCodeN.logicalX (2 * k + 3))
    (StabilizerGroup.RotatedSurfaceCodeN.logicalZ (2 * k + 3)) rfl rfl
    (StabilizerGroup.RotatedSurfaceCodeN.logicalX_anticommute_logicalZ (2 * k + 3))

end Quantum.SuperPoincareApplications
