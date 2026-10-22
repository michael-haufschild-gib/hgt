import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The expanding-frame annihilation of a fixed negative shift

Three elementary facts carry the expanding-frame argument.

The push-through identity is, on the spectral side, the partial-fraction split
`1 - r/(x+r) = x/(x+r)`: the defect of the resolvent mass is the mean of the bounded symbol
`x/(x+r)`.

The variational bound for a form that is coercive with two different constants on two complementary
blocks is a completion of squares on each block separately: `2xy - αx² ≤ y²/α`.  Summing the two
blocks gives the card's `‖Pu‖²/k + 2‖(1-P)u‖²/r`.

The source tail is a tail of a summable family, so it vanishes as the cutoff grows; and a sequence
of nonnegative numbers with no frequently-large subsequence converges to zero.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(304)`: the push-through identity on the spectral side -/

/-- **`(304)`: the defect of the resolvent mass is the mean of the bounded symbol.** -/
theorem one_sub_resolvent_mass {ν : Measure ℝ} [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ᵐ x ∂ν, 0 ≤ x) (hint : Integrable (fun x => 1 / (x + r)) ν) :
    1 - r * ∫ x, 1 / (x + r) ∂ν = ∫ x, x / (x + r) ∂ν := by
  have hint' : Integrable (fun x : ℝ => 1 - r * (1 / (x + r))) ν :=
    (integrable_const _).sub (hint.const_mul r)
  have hsplit : ∫ x, x / (x + r) ∂ν = ∫ x, (1 - r * (1 / (x + r))) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with x hx
    have h1 : (0 : ℝ) < x + r := by linarith
    field_simp
    ring
  rw [hsplit, integral_sub (integrable_const _) (hint.const_mul r), integral_const,
    MeasureTheory.integral_const_mul]
  simp

/-! ## `(309)`: the two-block variational bound -/

/-- Completion of squares on one block. -/
theorem two_mul_sub_sq_le {α x y : ℝ} (hα : 0 < α) : 2 * x * y - α * x ^ 2 ≤ y ^ 2 / α := by
  rw [le_div_iff₀ hα]
  nlinarith [sq_nonneg (α * x - y)]

/-- **`(309)`: a form coercive with two constants on complementary blocks has a variational inverse
bounded blockwise.** -/
theorem two_block_variational {α β x₁ x₂ y₁ y₂ : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    2 * (x₁ * y₁ + x₂ * y₂) - (α * x₁ ^ 2 + β * x₂ ^ 2) ≤ y₁ ^ 2 / α + y₂ ^ 2 / β := by
  have h1 := two_mul_sub_sq_le (α := α) (x := x₁) (y := y₁) hα
  have h2 := two_mul_sub_sq_le (α := β) (x := x₂) (y := y₂) hβ
  linarith

/-- The two-block coercivity constants of `(308)` are what the bound consumes. -/
theorem two_block_variational_of_coercive {Q α β x₁ x₂ y₁ y₂ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hQ : α * x₁ ^ 2 + β * x₂ ^ 2 ≤ Q) :
    2 * (x₁ * y₁ + x₂ * y₂) - Q ≤ y₁ ^ 2 / α + y₂ ^ 2 / β := by
  have h := two_block_variational (α := α) (β := β) (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂)
    hα hβ
  linarith

/-! ## `(311)`: the source tail vanishes -/

/-- **`(311)`: the high-block source mass vanishes as the cutoff grows.** -/
theorem tendsto_sourceTail_zero {ι : Type*} (w : ι → ℝ) :
    Tendsto (fun s : Finset ι => ∑' a : { x // x ∉ s }, w a) atTop (𝓝 0) :=
  tendsto_tsum_compl_atTop_zero w

/-! ## `(303)`: the negative parts vanish -/

/-- **`(303)`: a nonnegative sequence with no frequently-large values tends to zero.** -/
theorem tendsto_zero_of_not_frequently_ge {r : ℕ → ℝ} (hr : ∀ j, 0 ≤ r j)
    (h : ∀ r₀ : ℝ, 0 < r₀ → ¬ (∃ᶠ j in atTop, r₀ ≤ r j)) :
    Tendsto r atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have hev : ∀ᶠ j in atTop, ¬ (ε ≤ r j) := Filter.not_frequently.mp (h ε hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  have hlt : r n < ε := lt_of_not_ge (hN n hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hr n)]
  exact hlt

end GaloisForLFunctions.RHTower
