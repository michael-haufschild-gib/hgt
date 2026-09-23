import GaloisForLFunctions.RHTower.Sieve.MoebiusDyadicWindow
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDyadicDensity

/-!
# The block mean

The bilinear all-interval theorem compares the balanced pair sum with the square of the mean of `f`
over the dyadic block `(√x, 2√x]`.  Writing

    blockMean f x = (1/√x) ∑_{√x < n ≤ 2√x} f(n),

the two instances the card needs are already proved:

    blockMean μ x → 0,        blockMean μ² x → D = 6/π².

Both are the dyadic-window limits composed with `x ↦ √x`.
-/

namespace RHTower.Sieve

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

/-- The mean of `f` over the dyadic block `(√x, 2√x]`. -/
noncomputable def blockMean (f : ℕ → ℝ) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊2 * Real.sqrt x⌋₊, f n) / Real.sqrt x

/-- **The Möbius block mean vanishes.** -/
theorem tendsto_blockMean_moebius :
    Tendsto (blockMean (fun n : ℕ => ((μ n : ℤ) : ℝ))) atTop (𝓝 0) := by
  have hbase := tendsto_norm_sum_moebius_Ioc_div
  have hcomp := hbase.comp Real.tendsto_sqrt_atTop
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine hcomp.congr fun x => ?_
  simp only [Function.comp_apply, blockMean]
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
  congr 1
  have hcast : (∑ n ∈ Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊2 * Real.sqrt x⌋₊, ((μ n : ℤ) : ℂ))
      = ((∑ n ∈ Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊2 * Real.sqrt x⌋₊, ((μ n : ℤ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]

/-- **The squarefree block mean tends to the squarefree density.** -/
theorem tendsto_blockMean_moebius_sq :
    Tendsto (blockMean (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))) atTop (𝓝 squarefreeDensity) := by
  have hbase := tendsto_window_squarefree_density
  have hcomp := hbase.comp Real.tendsto_sqrt_atTop
  refine hcomp.congr fun x => ?_
  simp only [Function.comp_apply, blockMean]

end RHTower.Sieve
