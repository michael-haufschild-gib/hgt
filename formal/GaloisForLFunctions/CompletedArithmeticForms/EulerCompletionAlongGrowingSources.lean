import GaloisForLFunctions.CompletedArithmeticForms.EulerTerminalCost
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Explicit completion horizons for growing Euler sources

The source cutoff may vary arbitrarily. A quadratic coordinate horizon,
multiplied by the desired accuracy scale, controls the exact completion error.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.CompletedArithmeticForms
open _root_.RHTower.DeletionAveragedDivisor _root_.RHTower.DeletionCutoffAverage

/-- A coordinate horizon giving absolute completion allowance `δ`. -/
def eulerCompletionHorizon (M : ℕ) (δ : ℝ) : ℕ :=
  ⌈((M : ℝ) + 1) ^ 2 / δ⌉₊

/-- The explicit horizon gives the prescribed actual-source completion accuracy. -/
theorem fullErrorEnergy_finiteSource_error_le_at_explicit_horizon
    {X M : ℕ} (hX : 1 ≤ X) (hXM : X < M) {δ : ℝ} (hδ : 0 < δ) :
    |fullErrorEnergy X M -
      finiteSourceEnergy (errorIncrement X M) (eulerCompletionHorizon M δ)| ≤ δ := by
  apply fullErrorEnergy_finiteSource_error_le_of_horizon hX hXM
  have hceil : ((M : ℝ) + 1) ^ 2 / δ ≤ (eulerCompletionHorizon M δ : ℝ) := Nat.le_ceil _
  have h := (div_le_iff₀ hδ).mp hceil
  nlinarith only [h, hδ]

/-- The accuracy multiplier is independent of every source parameter. -/
def eulerCompletionSchedule (n M : ℕ) : ℕ := (n + 1) * (M + 1) ^ 2

theorem fullErrorEnergy_finiteSource_error_le_on_schedule
    {X M : ℕ} (hX : 1 ≤ X) (hXM : X < M) (n : ℕ) :
    |fullErrorEnergy X M -
      finiteSourceEnergy (errorIncrement X M) (eulerCompletionSchedule n M)| ≤
        1 / ((n : ℝ) + 1) := by
  apply fullErrorEnergy_finiteSource_error_le_of_horizon hX hXM
  rw [one_div, inv_mul_eq_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  simp only [eulerCompletionSchedule, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  nlinarith only [sq_nonneg ((M : ℝ) + 1)]

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.fullErrorEnergy_finiteSource_error_le_at_explicit_horizon
#print axioms GaloisForLFunctions.CompletedArithmeticForms.fullErrorEnergy_finiteSource_error_le_on_schedule
