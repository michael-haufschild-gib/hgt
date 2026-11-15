import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianCSSCodes
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.FiberCSSDistance

/-!
# Distance two on Hermitian fiber CSS groups

For `Q = 2^(s+2)`, the binary first-coordinate code on the actual
Hermitian affine curve gives a CSS group of length `Q³`, first-homology
dimension `Q³ - 2Q²`, and exact Pauli distance two. Each fiber has at
least four points, so two of its points support a nontrivial logical
operator. Increasing the curve size therefore increases the homology
dimension without increasing distance in this family.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis.Codes Quantum.Stabilizer.Homological

local instance squareBinaryDistanceFintype (s : ℕ) : Fintype (SquareConstantField 2 s) :=
  Fintype.ofFinite _
local instance hermitianBinaryDistanceFintype (s : ℕ) : Fintype (HermitianAffinePoints 2 s) :=
  Fintype.ofFinite _

/-- Every Hermitian fiber CSS group with `Q ≥ 4` has exact Pauli distance two. -/
theorem hermitianBinaryCSSStabilizerGroup_distance_two (s : ℕ) :
    (∀ g : Quantum.NQubitPauliGroupElement (hermitianBinaryHomologicalCode (s + 1)).numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        (hermitianBinaryCSSStabilizerGroup (s + 1)) →
        2 ≤ Quantum.NQubitPauliGroupElement.weight g) ∧
    ∃ g : Quantum.NQubitPauliGroupElement (hermitianBinaryHomologicalCode (s + 1)).numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        (hermitianBinaryCSSStabilizerGroup (s + 1)) ∧
        Quantum.NQubitPauliGroupElement.weight g = 2 := by
  have heven (b : SquareConstantField 2 (s + 1)) :
      2 ∣ Nat.card {i // hermitianFirstCoordinate 2 (s + 1) i = b} := by
    rw [hermitianFirstCoordinate_fiber_card]
    exact dvd_pow_self 2 (Nat.succ_ne_zero _)
  have hbig : 2 < Nat.card {i // hermitianFirstCoordinate 2 (s + 1) i = 0} := by
    rw [hermitianFirstCoordinate_fiber_card, pow_succ, pow_succ]
    have hpos : 0 < 2 ^ s := pow_pos (by decide) s
    omega
  exact fiberHomologicalCode_distance_two (hermitianFirstCoordinate 2 (s + 1)) heven 0 hbig

#print axioms hermitianBinaryCSSStabilizerGroup_distance_two
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
