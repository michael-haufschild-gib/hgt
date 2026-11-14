import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxIntegerResiduals
import GaloisForLFunctions.HTGeometry.FZZCigarWorldsheetDivisorGenusLock

/-!
# Uniform Gamma–Cox detection of the FZZ divisor constraint

The signed discrepancy between actual and required residual-zero counts is an
integer. Its unit gap makes classification uniform in genus, pole count, and
spectral flow, even when all these data change with concentration.
-/

open Filter Topology
open scoped Classical
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace GaloisForLFunctions.HTGeometry.FZZCigar
noncomputable section

/-- Signed error in the residual-zero count required by the divisor/genus relation. -/
def fzzIntegerResidual (g m s n : ℕ) : ℤ :=
  (m : ℤ) - fzzResidualZeroIndex g n s

/-- The integer residual vanishes exactly when the divisor constraint is realized. -/
theorem fzzIntegerResidual_zero_iff (g m s n : ℕ) :
    fzzIntegerResidual g m s n = 0 ↔ FZZDivisorRealization g m s n := by
  rw [fzzIntegerResidual, sub_eq_zero]
  exact (fzzDivisorRealization_iff_residualZeroIndex g m s n).symm

/-- The scalar detector tests the divisor/genus constraint without assuming its realization. -/
theorem cox_divisor_realization (g m s n : ℕ) :
    Tendsto (fun K => detection K (fzzIntegerResidual g m s n : ℝ)) atTop
      (𝓝 (if FZZDivisorRealization g m s n then 1 else 0)) := by
  simpa only [Int.cast_eq_zero, fzzIntegerResidual_zero_iff] using
    tendsto_detection (fzzIntegerResidual g m s n : ℝ)

/-- Arbitrarily moving finite families of topological data remain consistently classifiable. -/
theorem cox_moving_divisor_realization {ι : Type*} [Fintype ι]
    (g m s n : ℝ → ι → ℕ) :
    Tendsto (fun K => (binaryLaw K
      (fun i => (fzzIntegerResidual (g K i) (m K i) (s K i) (n K i) : ℝ))).real
      {b | b ≠ fun i => decide (FZZDivisorRealization (g K i) (m K i) (s K i) (n K i))})
      atTop (𝓝 0) := by
  exact tendsto_moving_integer_classification
    (fun K i => fzzIntegerResidual (g K i) (m K i) (s K i) (n K i))
    (fun K i => FZZDivisorRealization (g K i) (m K i) (s K i) (n K i))
    (fun K i => fzzIntegerResidual_zero_iff (g K i) (m K i) (s K i) (n K i))

/-- The finite-family error bound depends on family size, not on the topological counts. -/
theorem cox_divisor_error_le {ι : Type*} [Fintype ι] (K : ℝ) (g m s n : ι → ℕ) :
    (binaryLaw K (fun i => (fzzIntegerResidual (g i) (m i) (s i) (n i) : ℝ))).real
      {b | b ≠ fun i => decide (FZZDivisorRealization (g i) (m i) (s i) (n i))} ≤
        (Fintype.card ι : ℝ) * integerEnvelope (max K 0) := by
  have hp : zeroPattern (fun i => (fzzIntegerResidual (g i) (m i) (s i) (n i) : ℝ)) =
      fun i => decide (FZZDivisorRealization (g i) (m i) (s i) (n i)) := by
    funext i
    by_cases h : FZZDivisorRealization (g i) (m i) (s i) (n i)
    <;> simp [zeroPattern, fzzIntegerResidual_zero_iff, h]
  simpa only [hp] using
    binaryLaw_integer_error_le K (fun i => fzzIntegerResidual (g i) (m i) (s i) (n i))

/-- The number of tested sectors may grow with concentration, with no bound on their counts. -/
theorem cox_expanding_divisor_realization
    (g m s n : (k : ℕ) → Fin k → ℕ) :
    Tendsto (fun k : ℕ => (binaryLaw (k : ℝ)
      (fun i => (fzzIntegerResidual (g k i) (m k i) (s k i) (n k i) : ℝ))).real
      {b | b ≠ fun i => decide (FZZDivisorRealization (g k i) (m k i) (s k i) (n k i))})
      atTop (𝓝 0) := by
  exact tendsto_expanding_integer_classification
    (fun k i => fzzIntegerResidual (g k i) (m k i) (s k i) (n k i))
    (fun k i => FZZDivisorRealization (g k i) (m k i) (s k i) (n k i))
    (fun k i => fzzIntegerResidual_zero_iff (g k i) (m k i) (s k i) (n k i))

end
end GaloisForLFunctions.HTGeometry.FZZCigar

#print axioms GaloisForLFunctions.HTGeometry.FZZCigar.fzzIntegerResidual_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.FZZCigar.cox_divisor_realization
#print axioms GaloisForLFunctions.HTGeometry.FZZCigar.cox_moving_divisor_realization
#print axioms GaloisForLFunctions.HTGeometry.FZZCigar.cox_divisor_error_le
#print axioms GaloisForLFunctions.HTGeometry.FZZCigar.cox_expanding_divisor_realization
