import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianFiberCodes
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.BinaryCSSCodes

/-!
# Binary CSS groups on the actual Hermitian affine curve

For `Q = 2^(s+1)`, first-coordinate fibers on the Hermitian curve have
exactly `Q` points. Binary functions constant on these fibers form a
self-orthogonal code of length `Q³` and dimension `Q²`. The resulting
CSS complex has first-homology dimension `Q³ - 2Q²` and an actual
commuting Pauli stabilizer group.

This combines the finite-field curve counts with divisible-fiber
orthogonality and the homological CSS construction.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis.Codes Quantum.Stabilizer.Homological

local instance squareBinaryFintype (s : ℕ) : Fintype (SquareConstantField 2 s) :=
  Fintype.ofFinite _

local instance hermitianBinaryFintype (s : ℕ) : Fintype (HermitianAffinePoints 2 s) :=
  Fintype.ofFinite _

/-- Binary words constant on each first-coordinate fiber of the Hermitian curve. -/
def hermitianBinaryCoordinateCode (s : ℕ) :
    Submodule (ZMod 2) (HermitianAffinePoints 2 s → ZMod 2) :=
  fiberCode (hermitianFirstCoordinate 2 s)

/-- Even fiber sizes make the actual binary curve code self-orthogonal. -/
theorem hermitianBinaryCoordinateCode_selfOrthogonal (s : ℕ) :
    SelfOrthogonal (RingHom.id _) (hermitianBinaryCoordinateCode s) := by
  apply fiberCode_selfOrthogonal 2
  intro x
  rw [hermitianFirstCoordinate_fiber_card]
  exact dvd_pow_self 2 (Nat.succ_ne_zero s)

/-- One independent binary coordinate remains for each first-coordinate value. -/
theorem hermitianBinaryCoordinateCode_finrank (s : ℕ) :
    Module.finrank (ZMod 2) (hermitianBinaryCoordinateCode s) = 2 ^ (2 * (s + 1)) := by
  rw [hermitianBinaryCoordinateCode,
    fiberCode_finrank _ (hermitianFirstCoordinate_surjective 2 s),
    ← Nat.card_eq_fintype_card, squareConstantField_card]

/-- The symmetric CSS complex on actual Hermitian affine points. -/
def hermitianBinaryHomologicalCode (s : ℕ) : HomologicalCode :=
  selfOrthogonalHomologicalCode (hermitianBinaryCoordinateCode s)
    (hermitianBinaryCoordinateCode_selfOrthogonal s)

/-- The physical coordinates are exactly the `Q³` rational affine curve points. -/
theorem hermitianBinaryHomologicalCode_numQubits (s : ℕ) :
    (hermitianBinaryHomologicalCode s).numQubits = (2 ^ (s + 1)) ^ 3 := by
  change Fintype.card (HermitianAffinePoints 2 s) = _
  rw [← Nat.card_eq_fintype_card, hermitianAffinePoints_card]

/-- Exact first-homology dimension of the binary Hermitian fiber complex. -/
theorem hermitianBinaryHomologicalCode_finrank_H1 (s : ℕ) :
    Module.finrank (ZMod 2) (hermitianBinaryHomologicalCode s).H1 =
      (2 ^ (s + 1)) ^ 3 - 2 * (2 ^ (s + 1)) ^ 2 := by
  rw [hermitianBinaryHomologicalCode, selfOrthogonalHomologicalCode_finrank_H1,
    hermitianBinaryCoordinateCode_finrank, ← Nat.card_eq_fintype_card,
    hermitianAffinePoints_card, Nat.mul_comm 2 (s + 1), pow_mul]

/-- The actual Pauli stabilizer group associated to the binary Hermitian fiber code. -/
def hermitianBinaryCSSStabilizerGroup (s : ℕ) :
    Quantum.StabilizerGroup (hermitianBinaryHomologicalCode s).numQubits :=
  (hermitianBinaryHomologicalCode s).homologicalStabilizerGroup

#print axioms hermitianBinaryCoordinateCode_selfOrthogonal
#print axioms hermitianBinaryHomologicalCode_numQubits
#print axioms hermitianBinaryHomologicalCode_finrank_H1
#print axioms hermitianBinaryCSSStabilizerGroup

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
