import GaloisForLFunctions.CountingHolography.Sections.ThreeSquareConductorsWithZeroPoleDegree

/-! # The ordinary rational product over square conductors -/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset

/-- Multiplication is taken in the rationals, so prime factors cancel
across distinct conductors before the comparison is made. -/
def squareGeneratorPrefix (N : ℕ) : ℚ :=
  ∏ n ∈ Ioc 0 N, ordinaryPrimeGenerator (n • successorSquareTriple n)

theorem squareGeneratorPrefix_pos (N : ℕ) : 0 < squareGeneratorPrefix N := by
  apply prod_pos
  intro n _
  apply prod_pos
  intro k _
  exact zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _

#print axioms squareGeneratorPrefix_pos

end GaloisForLFunctions.CountingHolography.Sections
