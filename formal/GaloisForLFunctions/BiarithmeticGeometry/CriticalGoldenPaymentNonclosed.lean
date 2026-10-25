import GaloisForLFunctions.BiarithmeticGeometry.CriticalWienerLift
import GaloisForLFunctions.BiarithmeticGeometry.CriticalUnpaidSequence
import GaloisForLFunctions.BiarithmeticGeometry.GoldenPrimePayment

/-!
# Actual critical golden payment is not Wiener closed

The inverse-square-root-tail sequence lifts isometrically to the actual
critical Wiener algebra. Its finite zero-sum repairs converge in Wiener norm
to an unpaid kernel. The exact golden primary-tower identity transfers this
failure of closedness to the actual golden source at critical contact.
-/

noncomputable section
open Finset Filter Topology
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- An explicit norm-two critical Wiener kernel with unpaid partial-sum energy. -/
def criticalUnpaidWiener : WienerAlgebraAt (1 / 2) :=
  fiveCriticalWienerLift criticalUnpaidCoeff summable_abs_criticalUnpaidCoeff

/-- Finite critical repairing kernels approaching the explicit unpaid kernel. -/
def criticalFiniteWienerRepair (N : ℕ) : WienerAlgebraAt (1 / 2) :=
  fiveCriticalWienerLift (criticalFiniteRepair N) (summable_abs_criticalFiniteRepair N)

theorem norm_criticalUnpaidWiener : ‖criticalUnpaidWiener‖ = 2 := by
  rw [criticalUnpaidWiener, norm_fiveCriticalWienerLift, tsum_abs_criticalUnpaidCoeff]

/-- The actual Wiener distance is exactly twice the remaining inverse-square-root tail. -/
theorem criticalFiniteWienerRepair_distance (N : ℕ) :
    ‖criticalFiniteWienerRepair N - criticalUnpaidWiener‖ = 2 * criticalUnpaidTail N := by
  rw [criticalFiniteWienerRepair, criticalUnpaidWiener, norm_fiveCriticalWienerLift_sub,
    criticalFiniteRepair_distance]

theorem criticalFiniteWienerRepair_tendsto :
    Tendsto criticalFiniteWienerRepair atTop (𝓝 criticalUnpaidWiener) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [criticalFiniteWienerRepair_distance]
  simpa only [mul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
      criticalUnpaidTail_tendsto

private theorem mem_golden_critical_realLift_iff (g : ℕ → ℝ)
    (hg : Summable fun r => |g r|) :
    fiveCriticalWienerLift g hg ∈ paidIdeal (goldenArithmeticSource goldenCriticalParameter)
      (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
        goldenCriticalParameter_bounds.2.le) ↔
      Summable (fun M : ℕ => (∑ r ∈ range (M + 1), g r) ^ 2) := by
  rw [paidIdeal_goldenArithmeticSource _ goldenCriticalParameter_bounds.1.le
    goldenCriticalParameter_bounds.2.le]
  simpa only [golden_primary_at_critical] using
    (mem_paidIdeal_critical_fiveCriticalWienerLift_iff g hg)

/-- Every member of the finite approximation sequence repairs the actual critical golden source. -/
theorem criticalFiniteWienerRepair_mem_golden_paidIdeal (N : ℕ) :
    criticalFiniteWienerRepair N ∈ paidIdeal (goldenArithmeticSource goldenCriticalParameter)
      (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
        goldenCriticalParameter_bounds.2.le) :=
  (mem_golden_critical_realLift_iff _ _).mpr (summable_sq_criticalFiniteRepair_partialSum N)

/-- Its actual Wiener limit does not repair the same source. -/
theorem criticalUnpaidWiener_not_mem_golden_paidIdeal :
    criticalUnpaidWiener ∉ paidIdeal (goldenArithmeticSource goldenCriticalParameter)
      (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
        goldenCriticalParameter_bounds.2.le) := by
  rw [criticalUnpaidWiener, mem_golden_critical_realLift_iff]
  exact not_summable_sq_criticalUnpaidCoeff_partialSum

/-- Critical golden payment fails ambient Wiener closedness, witnessed by explicit finite repairs. -/
theorem not_isClosed_golden_critical_paidIdeal :
    ¬IsClosed ((paidIdeal (goldenArithmeticSource goldenCriticalParameter)
      (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
        goldenCriticalParameter_bounds.2.le)) : Set (WienerAlgebraAt (1 / 2))) := by
  intro hclosed
  exact criticalUnpaidWiener_not_mem_golden_paidIdeal
    (hclosed.mem_of_tendsto criticalFiniteWienerRepair_tendsto
      (Eventually.of_forall criticalFiniteWienerRepair_mem_golden_paidIdeal))

end GaloisForLFunctions.BiarithmeticGeometry
