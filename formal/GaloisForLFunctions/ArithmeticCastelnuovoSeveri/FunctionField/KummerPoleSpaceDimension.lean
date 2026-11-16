import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleSpaceCoordinates
import GaloisForLFunctions.HTGeometry.PureFibreTangentIso
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimensions of one-point Kummer pole spaces

The explicit character coordinates make every bounded-pole space
finite-dimensional. Its dimension is the sum of the independent
polynomial-degree cutoffs, giving the full one-point Hilbert function.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r m : ℕ)

/-- Every one-point pole space of the actual Kummer field is finite-dimensional. -/
instance squareKummer_poleSpace_finiteDimensional :
    FiniteDimensional (SquareConstantField p s) (squareKummerPoleSpace p s c d r m) :=
  Module.Finite.equiv (squareKummerPoleSpaceCoordinateEquiv p s c d r m)

/-- The one-point Hilbert function is the sum of the explicit character cutoffs. -/
theorem squareKummer_poleSpace_finrank :
    Module.finrank (SquareConstantField p s) (squareKummerPoleSpace p s c d r m) =
      ∑ i : Fin (p ^ (s + 1) + 1), kummerPoleCutoff p s d r m i.val := by
  rw [← (squareKummerPoleSpaceCoordinateEquiv p s c d r m).finrank_eq]
  change Module.finrank (SquareConstantField p s)
    ((i : Fin (p ^ (s + 1) + 1)) →
      degreeLT (SquareConstantField p s) (kummerPoleCutoff p s d r m i.val)) = _
  rw [Module.finrank_pi_fintype]
  simp only [GaloisForLFunctions.HTGeometry.finrank_degreeLT]

/-- The functions with no pole anywhere form a one-dimensional space over the constants. -/
theorem squareKummer_poleSpace_zero_finrank :
    Module.finrank (SquareConstantField p s) (squareKummerPoleSpace p s c d r 0) = 1 := by
  rw [squareKummer_poleSpace_finrank, Fin.sum_univ_eq_sum_range]
  simp only [kummerPoleCutoff_zero, Finset.sum_ite_eq', Finset.mem_range,
    Nat.succ_pos, if_true]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
