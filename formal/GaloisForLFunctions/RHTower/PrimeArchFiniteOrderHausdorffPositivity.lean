import GaloisForLFunctions.RHTower.PrimeArchHausdorffFixedOrderLargeShiftPositivity
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Simultaneous Hausdorff positivity at finitely many orders

The maximum of the established row thresholds is a common shift for any finite
set of orders. The threshold depends on that finite set; no bound uniform over
all orders or effective numerical value is asserted.
-/

namespace RHTower
noncomputable section
set_option autoImplicit false

/-- A common threshold for a finite collection of literal prime–archimedean rows. -/
def finiteHausdorffShift (S : Finset ℕ) : ℕ :=
  S.sup primeArchHausdorffShiftThreshold

theorem finiteHausdorffShift_le_iff (S : Finset ℕ) (r : ℕ) :
    finiteHausdorffShift S ≤ r ↔ ∀ j ∈ S, primeArchHausdorffShiftThreshold j ≤ r :=
  Finset.sup_le_iff

theorem finiteHausdorffShift_union (S T : Finset ℕ) :
    finiteHausdorffShift (S ∪ T) = max (finiteHausdorffShift S) (finiteHausdorffShift T) :=
  Finset.sup_union

theorem finiteHausdorffShift_monotone : Monotone finiteHausdorffShift := by
  intro S T h
  exact Finset.sup_mono h

/-- Every selected order is nonnegative at every shift beyond the common threshold. -/
theorem scaledHausdorffMomentDifference_nonneg_finiteShift
    (S : Finset ℕ) (j : S) (r : ℕ) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment j (finiteHausdorffShift S + r) := by
  have hj : primeArchHausdorffShiftThreshold j ≤ finiteHausdorffShift S :=
    Finset.le_sup j.property
  apply scaledHausdorffMomentDifference_nonneg_of_shiftThreshold_le
  omega

/-- Common threshold for all orders from zero through `n`. -/
def finiteOrderHausdorffShift (n : ℕ) : ℕ :=
  finiteHausdorffShift (Finset.range (n + 1))

/-- A symbolic sign certificate for the entire prescribed finite block of orders. -/
theorem scaledHausdorffMomentDifference_nonneg_finiteOrder
    (n r : ℕ) (j : Fin (n + 1)) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment j (finiteOrderHausdorffShift n + r) := by
  exact scaledHausdorffMomentDifference_nonneg_finiteShift (Finset.range (n + 1))
    ⟨j.val, Finset.mem_range.mpr j.isLt⟩ r

end
end RHTower
