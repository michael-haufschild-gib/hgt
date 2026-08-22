import GaloisForLFunctions.HTGeometry.FiniteUnitaryEuclideanExponentialWordAnalytic
import GaloisForLFunctions.HTGeometry.HaferkampSpecialUnitaryPauliMultichart

/-!
# A globally centred Pauli/exponential atlas for finite two-qubit special unitaries

The rank-fifteen Pauli chart is placed on the left of a uniform Euclidean exponential word.  The
determinant normalizer is left-`SU(4)` equivariant, so this hybrid chart has the Pauli chart as an
exact slice at every globally covered centre.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One Euclidean self-adjoint coordinate block for a two-qubit unitary exponential. -/
abbrev boolTwoQubitSelfAdjointCoordinates :=
  Fin (Module.finrank ℝ (selfAdjoint (Matrix (Bool × Bool) (Bool × Bool) ℂ))) → ℝ

/-- Ordered Euclidean exponential coordinates for a finite two-qubit word. -/
abbrev boolTwoQubitEuclideanWordCoordinates (N : ℕ) :=
  Fin N → boolTwoQubitSelfAdjointCoordinates

/-- The Pauli chart followed by a finite Euclidean unitary exponential word and determinant
normalization. -/
def boolNonidentityTwoQubitPauliHybridAtlas (N : ℕ)
    (x : boolNonidentityTwoQubitPauliLabel → ℝ)
    (Y : boolTwoQubitEuclideanWordCoordinates N) :
    Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  specialUnitaryNormalize (false, false)
    (specialUnitaryToUnitary (boolNonidentityTwoQubitPauliCoordinateGate x) *
      finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y)

/-- Left equivariance makes the Pauli chart an exact factor of the hybrid atlas. -/
theorem boolNonidentityTwoQubitPauliHybridAtlas_eq
    (N : ℕ) (x : boolNonidentityTwoQubitPauliLabel → ℝ)
    (Y : boolTwoQubitEuclideanWordCoordinates N) :
    boolNonidentityTwoQubitPauliHybridAtlas N x Y =
      boolNonidentityTwoQubitPauliCoordinateGate x *
        specialUnitaryNormalize (false, false)
          (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y) := by
  exact specialUnitaryNormalize_mul_left (false, false)
    (boolNonidentityTwoQubitPauliCoordinateGate x)
    (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y)

/-- At zero Pauli coordinates, the hybrid atlas is its normalized Euclidean word. -/
theorem boolNonidentityTwoQubitPauliHybridAtlas_zero
    (N : ℕ)
    (Y : boolTwoQubitEuclideanWordCoordinates N) :
    boolNonidentityTwoQubitPauliHybridAtlas N 0 Y =
      specialUnitaryNormalize (false, false)
        (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y) := by
  rw [boolNonidentityTwoQubitPauliHybridAtlas_eq,
    boolNonidentityTwoQubitPauliCoordinateGate_zero, one_mul]

/-- One finite word length places a Pauli-chart centre at every element of `SU(4)`. -/
theorem exists_boolNonidentityTwoQubitPauliHybridAtlas_center
    : ∃ N : ℕ, ∀ S : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ Y : boolTwoQubitEuclideanWordCoordinates N,
        boolNonidentityTwoQubitPauliHybridAtlas N 0 Y = S := by
  obtain ⟨N, hN⟩ :=
    exists_finiteSpecialUnitary_uniform_normalizedEuclideanExponentialWord
      (Bool × Bool) (false, false)
  refine ⟨N, fun S => ?_⟩
  obtain ⟨Y, hY⟩ := hN S
  refine ⟨Y, ?_⟩
  rw [boolNonidentityTwoQubitPauliHybridAtlas_zero]
  exact hY

end

end GaloisForLFunctions.HTGeometry
