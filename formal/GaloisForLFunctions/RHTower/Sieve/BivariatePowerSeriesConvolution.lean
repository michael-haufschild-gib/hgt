import GaloisForLFunctions.RHTower.Sieve.SelbergPrincipalPrimePowerValues
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Bivariate generating series and additive convolution

A real array `f : ℕ → ℕ → ℝ` is encoded as the iterated power series
`∑_i (∑_j f(i, j) Y^j) X^i ∈ ℝ⟦Y⟧⟦X⟧`. The additive bivariate convolution
`(f * g)(i, j) = ∑_{a ≤ i, b ≤ j} f(a, b) g(i - a, j - b)` is exactly the coefficient array of the
product of the generating series, and the encoding is injective.

## Main results

- `coeff_mul_bivariateCoefficientSeries`: the `(i, j)` coefficient of a product of generating
  series is the additive convolution at `(i, j)`.
- `bivariateCoefficientSeries_convolution`: the generating series of `f * g` is the product of the
  generating series.
- `bivariateCoefficientSeries_injective`: the encoding is injective.

## Hypotheses

All results are unconditional identities.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Generating series `∑_i (∑_j f(i, j) Y^j) X^i` of a bivariate real array. -/
def bivariateCoefficientSeries (f : ℕ → ℕ → ℝ) : PowerSeries (PowerSeries ℝ) :=
  PowerSeries.mk (fun i => PowerSeries.mk (f i))

@[simp] theorem coeff_bivariateCoefficientSeries (f : ℕ → ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (bivariateCoefficientSeries f)) = f i j := by
  simp [bivariateCoefficientSeries]

/-- Additive (Cauchy) bivariate convolution `∑_{a ≤ i, b ≤ j} f(a, b) g(i - a, j - b)`. -/
def additiveBivariateConvolution (f g : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
    f a b * g (i - a) (j - b)

/-- The `(i, j)` coefficient of the product of two generating series is the additive convolution
of the arrays at `(i, j)`. -/
theorem coeff_mul_bivariateCoefficientSeries (f g : ℕ → ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff j
        (PowerSeries.coeff i (bivariateCoefficientSeries f * bivariateCoefficientSeries g)) =
      additiveBivariateConvolution f g i j := by
  rw [PowerSeries.coeff_mul]
  simp only [map_sum]
  rw [show (∑ x ∈ Finset.HasAntidiagonal.antidiagonal i,
      PowerSeries.coeff j
        (PowerSeries.coeff x.1 (bivariateCoefficientSeries f) *
          PowerSeries.coeff x.2 (bivariateCoefficientSeries g))) =
      ∑ a ∈ Finset.range (i + 1), PowerSeries.coeff j
        (PowerSeries.coeff a (bivariateCoefficientSeries f) *
          PowerSeries.coeff (i - a) (bivariateCoefficientSeries g)) by
      simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff j
          (PowerSeries.coeff a (bivariateCoefficientSeries f) *
            PowerSeries.coeff b (bivariateCoefficientSeries g))) i]
  simp only [PowerSeries.coeff_mul, coeff_bivariateCoefficientSeries]
  rw [additiveBivariateConvolution]
  apply Finset.sum_congr rfl
  intro a ha
  simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun b c => f a b * g (i - a) c) j

/-- The generating series turns additive bivariate convolution into multiplication. -/
theorem bivariateCoefficientSeries_convolution (f g : ℕ → ℕ → ℝ) :
    bivariateCoefficientSeries (additiveBivariateConvolution f g) =
      bivariateCoefficientSeries f * bivariateCoefficientSeries g := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  rw [coeff_bivariateCoefficientSeries, coeff_mul_bivariateCoefficientSeries]

/-- Distinct arrays have distinct generating series. -/
theorem bivariateCoefficientSeries_injective :
    Function.Injective bivariateCoefficientSeries := by
  intro f g h
  funext i j
  have hc := congrArg (fun F => PowerSeries.coeff j (PowerSeries.coeff i F)) h
  simpa using hc

end

end RHTower.Sieve
