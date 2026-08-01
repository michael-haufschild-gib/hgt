import GaloisForLFunctions.RHTower.SoninShellCutHighSlackProduct

/-!
# The high-side slack vanishes in its product

The high-side radicand is a constant times the product of half-width and radius raised to one minus
twice the decay order, an exponent that is negative from the first order on.  So the radicand — and
with it the term — tends to zero as that product grows.

This is the third and last of the slack terms to be given a vanishing, and like the middle one it
vanishes in the schedule constant rather than in the number of annuli.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- The negative power vanishes at infinity. -/
theorem tendsto_rpow_one_sub_two_mul_atTop {N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    Tendsto (fun u : ℝ => u ^ (1 - (2 * N₀ : ℝ))) atTop (𝓝 0) := by
  have hpos : (0 : ℝ) < (2 * N₀ : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
    linarith
  have hbase := tendsto_rpow_neg_atTop hpos
  refine hbase.congr fun u => ?_
  congr 1
  ring

/-- **The high-side slack vanishes.**  The root of a constant times a negative power of the product
tends to zero as the product grows. -/
theorem tendsto_sqrt_const_mul_rpow_atTop (C : ℝ) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    Tendsto (fun u : ℝ => Real.sqrt (C * u ^ (1 - (2 * N₀ : ℝ)))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun u : ℝ => C * u ^ (1 - (2 * N₀ : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_rpow_one_sub_two_mul_atTop hN₀).const_mul C
    rw [mul_zero] at this
    exact this
  have := (Real.continuous_sqrt.tendsto 0).comp hbase
  simpa [Function.comp_def, Real.sqrt_zero] using this

end RHTower
