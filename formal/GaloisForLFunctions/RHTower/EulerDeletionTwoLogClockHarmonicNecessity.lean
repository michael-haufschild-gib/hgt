import GaloisForLFunctions.RHTower.EulerDeletionTwoLogClockRHEndpoint
import GaloisForLFunctions.RHTower.EulerDeletionPhysicalCellMoebiusIdentity

/-!
# The reciprocal-Möbius obstruction survives the two-logarithm projection

The smaller signed quotient field still pays for the literal fixed-start
harmonic source on the untouched initial physical cells. Projection cannot
hide that RH-strength scalar by averaging over its much larger clock fibres.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace RHTower.DeletionResidueMartingale

theorem reciprocal_moebius_tail_sq_mul_le_twoLogClockProjection_energy (N : ℕ) :
    (N : ℝ) *
      (∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)) ^ (2 : ℕ) ≤
      4 * ‖(historySpace (twoLogClockThreshold N)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) +
      12 * (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) + 4 := by
  have hphysical := RHTower.reciprocal_moebius_tail_sq_mul_le_physical_energy N
  have hsource := source_energy_le_twoLogClockProjection_energy_add_log N
  rw [← sourceVec_energy] at hphysical
  nlinarith

end RHTower.DeletionResidueMartingale
