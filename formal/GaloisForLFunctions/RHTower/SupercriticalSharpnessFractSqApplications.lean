import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.RHTower.FractSqConstSeries

/-!
# Supercritical sharpness density selection for fractional-part cells

The disjoint integer cells used to evaluate the squared-fractional-part constant form another
literal slab family.  Among first `M` cells, one carries at least average integral mass.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Integral mass in one squared-fractional-part tail cell. -/
def fractSqCellMass (n : ℕ) : ℝ :=
  ∫ v in tailCell n, fractSqInvSq v

/-- Elementary closed form of one squared-fractional-part cell mass. -/
def fractSqClosedCellTerm (n : ℕ) : ℝ :=
  1 + ((n : ℝ) + 1) / ((n : ℝ) + 2)
    - 2 * ((n : ℝ) + 1) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1))

theorem fractSqCellMass_eq_closedCellTerm (n : ℕ) :
    fractSqCellMass n = fractSqClosedCellTerm n := by
  exact integral_tailCell_fractSqInvSq n

/-- Among first `M` disjoint fractional-part cells, either family is empty or one cell carries at
least average mass. -/
theorem fractSqCellMass_empty_or_exists_averageHeavy (M : ℕ) :
    M = 0 ∨ ∃ n : Fin M,
      (∑ j : Fin M, fractSqCellMass j) ≤ (M : ℝ) * fractSqCellMass n := by
  simpa only [Fintype.card_fin] using
    (GaloisForLFunctions.HTGeometry.finiteFamilySum_empty_or_le_card_mul
      (fun n : Fin M ↦ fractSqCellMass n))

/-- The same average-heavy-cell certificate in the elementary closed form of each cell mass. -/
theorem fractSqClosedCellTerm_empty_or_exists_averageHeavy (M : ℕ) :
    M = 0 ∨ ∃ n : Fin M,
      (∑ j : Fin M, fractSqClosedCellTerm j) ≤
        (M : ℝ) * fractSqClosedCellTerm n := by
  simpa only [fractSqCellMass_eq_closedCellTerm] using
    fractSqCellMass_empty_or_exists_averageHeavy M

end RHTower
