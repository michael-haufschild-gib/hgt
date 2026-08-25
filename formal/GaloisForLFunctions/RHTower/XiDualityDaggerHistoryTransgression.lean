import GaloisForLFunctions.RHTower.RiemannBoundaryGreenFractureLaw
import GaloisForLFunctions.RHTower.XiSourceHistoryResidueTransgression

/-!
# Xi duality--dagger history transgression

The completed Xi source already carries functional-equation duality, a positive oriented Hodge
dagger, and source repair histories.  This module proves they do not merely vanish on the same
locus: their local defects are one coefficient in two categorical degrees.

For the canonical oriented atom whose Hodge image is the unit coordinate at a divisor copy,
the Frobenius--Hodge commutator is exactly the source-inverse/analytic-adjoint fracture.  The
metric holonomy between the two executable repair histories is then `log(clock)` times that
commutator.  Thus history confluence and dagger naturality are exact transgressions of one
signed anomaly, not separate RH criteria.

No RH, zero-location, positivity, simplicity, or fitted comparison hypothesis is used.
-/

open Complex
open GaloisForLFunctions

namespace RHTower

open ConstitutiveCriticalCompletionMechanics

noncomputable section

/-- Canonical atom whose oriented Hodge image has coefficient one at `q`. -/
def deningerArithmeticOrientedHodgeUnitAt (q : XiZeroCopy) :
    DeningerArithmeticGradedH1 :=
  Finsupp.single (xiZeroCopyReflectEquiv q)
    (-deningerArithmeticFEOrientation q)

@[simp]
theorem deningerArithmeticOrientedHodgeUnitAt_hodge_apply
    (q : XiZeroCopy) :
    deningerArithmeticGradedOrientedHodge.sigma
        (deningerArithmeticOrientedHodgeUnitAt q) q = 1 := by
  rw [deningerArithmeticGradedOrientedHodge_apply]
  simp only [deningerArithmeticOrientedHodgeUnitAt,
    Finsupp.single_eq_same, map_neg,
    deningerArithmeticFEOrientation_conj]
  have hsq := deningerArithmeticFEOrientation_sq q
  linear_combination hsq

/-- The canonical oriented atom reads the duality--adjunction fracture exactly. -/
theorem deningerArithmeticOrientedHodgeUnitAt_commutator_eq_fracture
    (q : XiZeroCopy) :
    (deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticOrientedHodgeUnitAt q)) -
        deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedTheta
            (deningerArithmeticOrientedHodgeUnitAt q))) q =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) := by
  rw [deningerArithmeticOrientedHodge_commutator_apply_eq_boundaryFracture,
    deningerArithmeticOrientedHodgeUnitAt_hodge_apply, mul_one]

/-- Source-history holonomy is logarithmic clock times duality--dagger curvature. -/
theorem actualRepairHistoryDefect_eq_log_mul_orientedHodgeCommutator
    (N clock : ℕ) (q : XiZeroCopy) :
    ((actualRepairOrientationPotential N clock (q.1 : ℂ) (left (N + 1)) -
          actualRepairOrientationPotential N clock (q.1 : ℂ) (right (N + 1)) : ℝ) : ℂ) =
      (Real.log clock : ℂ) *
        ((deningerArithmeticGradedTheta
              (deningerArithmeticGradedOrientedHodge.sigma
                (deningerArithmeticOrientedHodgeUnitAt q)) -
            deningerArithmeticGradedOrientedHodge.sigma
              (deningerArithmeticGradedTheta
                (deningerArithmeticOrientedHodgeUnitAt q))) q) := by
  rw [actualRepairHistoryDefect_eq_shellTransferEntropy,
    deningerArithmeticOrientedHodgeUnitAt_commutator_eq_fracture,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re,
    shellTransferEntropy_eq]
  norm_num
  ring

/-- At every nontrivial clock, history confluence and dagger naturality fail together. -/
theorem actualRepairHistoryDefect_zero_iff_orientedHodgeCommutator_zero
    (N clock : ℕ) (hclock : 2 ≤ clock) (q : XiZeroCopy) :
    (((actualRepairOrientationPotential N clock (q.1 : ℂ) (left (N + 1)) -
          actualRepairOrientationPotential N clock (q.1 : ℂ) (right (N + 1)) : ℝ) : ℂ) = 0) ↔
      ((deningerArithmeticGradedTheta
            (deningerArithmeticGradedOrientedHodge.sigma
              (deningerArithmeticOrientedHodgeUnitAt q)) -
          deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticGradedTheta
              (deningerArithmeticOrientedHodgeUnitAt q))) q = 0) := by
  rw [actualRepairHistoryDefect_eq_log_mul_orientedHodgeCommutator]
  have hclockReal : (1 : ℝ) < clock := by
    exact_mod_cast (lt_of_lt_of_le one_lt_two hclock)
  have hlogReal : Real.log (clock : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hclockReal)
  have hlog : (Real.log clock : ℂ) ≠ 0 := by
    exact_mod_cast hlogReal
  constructor
  · intro hproduct
    exact (mul_eq_zero.mp hproduct).resolve_left hlog
  · intro hzero
    rw [hzero, mul_zero]

end

end RHTower
