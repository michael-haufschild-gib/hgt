import GaloisForLFunctions.CompletedArithmeticForms.EulerTerminalCost
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

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

/-- The signed terminal discrepancy survives the same uniform schedule. -/
theorem fullErrorEnergy_freeTerminal_schur_bound_on_schedule
    {X M : ℕ} (hX : 1 ≤ X) (hXM : X < M) (b : ℕ → ℝ) (n : ℕ) :
    let T := eulerCompletionSchedule n M
    2 * (∑ j ∈ Icc 1 T, errorIncrement X M j * b j) - fullErrorEnergy X M ≤
      finiteSourceDualCost b T -
        ((∑ j ∈ Icc 1 T, errorIncrement X M j) - (T : ℝ) * b T) ^ 2 /
          ((T : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
  have hs := finiteSourceEnergy_schur_bound_with_mass (errorIncrement X M) b
    (eulerCompletionSchedule n M)
  have he := (abs_le.mp
    (fullErrorEnergy_finiteSource_error_le_on_schedule hX hXM n)).1
  dsimp only
  linarith only [hs, he]

/-- Arbitrarily growing source cutoffs still have vanishing completion error. -/
theorem tendsto_fullErrorEnergy_sub_finiteSourceEnergy_on_schedule
    (X M : ℕ → ℕ) (hX : ∀ n, 1 ≤ X n) (hXM : ∀ n, X n < M n) :
    Tendsto (fun n => fullErrorEnergy (X n) (M n) -
      finiteSourceEnergy (errorIncrement (X n) (M n)) (eulerCompletionSchedule n (M n)))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm
    (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [Real.norm_eq_abs] using
    fullErrorEnergy_finiteSource_error_le_on_schedule (hX n) (hXM n) n

/-- Completion preserves every finite energy limit along arbitrary source schedules. -/
theorem tendsto_fullErrorEnergy_iff_finiteSourceEnergy_on_schedule
    (X M : ℕ → ℕ) (hX : ∀ n, 1 ≤ X n) (hXM : ∀ n, X n < M n) (L : ℝ) :
    Tendsto (fun n => fullErrorEnergy (X n) (M n)) atTop (𝓝 L) ↔
      Tendsto (fun n => finiteSourceEnergy (errorIncrement (X n) (M n))
        (eulerCompletionSchedule n (M n))) atTop (𝓝 L) := by
  have he := tendsto_fullErrorEnergy_sub_finiteSourceEnergy_on_schedule X M hX hXM
  constructor
  · intro h
    simpa only [sub_sub_cancel, sub_zero] using h.sub he
  · intro h
    simpa only [sub_add_cancel, zero_add] using he.add h

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.fullErrorEnergy_finiteSource_error_le_at_explicit_horizon
#print axioms GaloisForLFunctions.CompletedArithmeticForms.fullErrorEnergy_finiteSource_error_le_on_schedule
#print axioms GaloisForLFunctions.CompletedArithmeticForms.fullErrorEnergy_freeTerminal_schur_bound_on_schedule
#print axioms GaloisForLFunctions.CompletedArithmeticForms.tendsto_fullErrorEnergy_iff_finiteSourceEnergy_on_schedule
