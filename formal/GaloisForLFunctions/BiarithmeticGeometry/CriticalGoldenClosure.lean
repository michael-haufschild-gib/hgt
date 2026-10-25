import GaloisForLFunctions.BiarithmeticGeometry.ComplexCriticalWienerLift
import GaloisForLFunctions.BiarithmeticGeometry.CriticalPartialSumCore

/-!
# Zero evaluation supplies actual critical golden closure classes

Corrected finite complex coefficients give actual paid Wiener kernels.
The exact coefficient-distance formula transfers through the isometric
lift. Every zero-evaluation one-prime kernel therefore belongs to the
closure of the full actual golden paid ideal.
-/

noncomputable section
open Finset Filter Topology
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Corrected finite coefficients lifted into the actual critical Wiener algebra. -/
def criticalCorrectedWiener (g : ℕ → ℂ) (N : ℕ) : WienerAlgebraAt (1 / 2) :=
  fiveComplexCriticalWienerLift (criticalCorrectedTruncation g N)
    (summable_norm_criticalCorrectedTruncation g N)

/-- Every corrected finite lift pays the actual critical golden source. -/
theorem criticalCorrectedWiener_mem_paidIdeal (g : ℕ → ℂ) (N : ℕ) :
    criticalCorrectedWiener g N ∈ paidIdeal (goldenArithmeticSource goldenCriticalParameter)
      (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
        goldenCriticalParameter_bounds.2.le) := by
  rw [criticalCorrectedWiener, mem_golden_critical_fiveComplexCriticalWienerLift_iff]
  exact summable_sq_partialSum_criticalCorrectedTruncation g N

/-- The actual Wiener approximation error converges to the absolute total evaluation. -/
theorem criticalCorrectedWiener_norm_error_tendsto (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) :
    Tendsto (fun N => ‖criticalCorrectedWiener g N - fiveComplexCriticalWienerLift g hg‖)
      atTop (𝓝 ‖∑' r, g r‖) := by
  simp only [criticalCorrectedWiener, norm_fiveComplexCriticalWienerLift_sub]
  exact criticalCorrectedTruncation_norm_error_tendsto g hg

/-- Zero evaluation gives norm convergence of actual finite paid kernels. -/
theorem criticalCorrectedWiener_tendsto (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) (hzero : (∑' r, g r) = 0) :
    Tendsto (criticalCorrectedWiener g) atTop (𝓝 (fiveComplexCriticalWienerLift g hg)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [hzero, norm_zero] using criticalCorrectedWiener_norm_error_tendsto g hg

/-- Every zero-evaluation one-prime kernel lies in the full actual golden payment closure. -/
theorem fiveComplexCriticalWienerLift_mem_closure_paidIdeal (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) (hzero : (∑' r, g r) = 0) :
    fiveComplexCriticalWienerLift g hg ∈ closure
      ((paidIdeal (goldenArithmeticSource goldenCriticalParameter)
        (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
          goldenCriticalParameter_bounds.2.le)) : Set (WienerAlgebraAt (1 / 2))) :=
  isClosed_closure.mem_of_tendsto (criticalCorrectedWiener_tendsto g hg hzero)
    (Eventually.of_forall fun N => subset_closure (criticalCorrectedWiener_mem_paidIdeal g N))

end GaloisForLFunctions.BiarithmeticGeometry

