import GaloisForLFunctions.RHTower.Sieve.BivariatePowerSeriesConvolution

/-!
# Algebra of additive bivariate convolution

Through the injective generating-series map `f ↦ ∑ f(i, j) X^i Y^j` into iterated power series, which sends
additive bivariate convolution to multiplication, the convolution of real arrays on `ℕ × ℕ`
inherits the commutative ring laws. The module records that the series map is additive and sends
the unit array to `1`, and derives associativity, commutativity, the unit laws and distributivity
over subtraction of the convolution.

## Main results

- `bivariateCoefficientSeries_one`, `bivariateCoefficientSeries_add`,
  `bivariateCoefficientSeries_sub`: the series map preserves `1`, sums and differences.
- `additiveBivariateConvolution_assoc`, `additiveBivariateConvolution_comm`: convolution is
  associative and commutative.
- `additiveBivariateConvolution_one_left`, `additiveBivariateConvolution_one_right`: the array
  `δ_{(0,0)}` is a two-sided unit.
- `additiveBivariateConvolution_sub_left`, `additiveBivariateConvolution_sub_right`: convolution
  distributes over subtraction.

## Hypotheses

All results are unconditional identities.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- The unit array `δ_{(0,0)}` for additive bivariate convolution. -/
def additiveBivariateOne (i j : ℕ) : ℝ :=
  if i = 0 ∧ j = 0 then 1 else 0

theorem bivariateCoefficientSeries_zero :
    bivariateCoefficientSeries (fun _ _ => 0) = 0 := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp

/-- The generating series of the unit array is `1`. -/
theorem bivariateCoefficientSeries_one :
    bivariateCoefficientSeries additiveBivariateOne = 1 := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  rw [coeff_bivariateCoefficientSeries]
  rw [PowerSeries.coeff_one]
  by_cases hi : i = 0
  · rw [if_pos hi, PowerSeries.coeff_one]
    simp [additiveBivariateOne, hi]
  · rw [if_neg hi]
    simp [additiveBivariateOne, hi]

/-- The generating series map is additive. -/
theorem bivariateCoefficientSeries_add (f g : ℕ → ℕ → ℝ) :
    bivariateCoefficientSeries (fun i j => f i j + g i j) =
      bivariateCoefficientSeries f + bivariateCoefficientSeries g := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp

/-- The generating series map commutes with subtraction. -/
theorem bivariateCoefficientSeries_sub (f g : ℕ → ℕ → ℝ) :
    bivariateCoefficientSeries (fun i j => f i j - g i j) =
      bivariateCoefficientSeries f - bivariateCoefficientSeries g := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp

/-- Additive bivariate convolution is associative. -/
theorem additiveBivariateConvolution_assoc (f g h : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution (additiveBivariateConvolution f g) h =
      additiveBivariateConvolution f (additiveBivariateConvolution g h) := by
  apply bivariateCoefficientSeries_injective
  rw [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_convolution,
    bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_convolution, mul_assoc]

/-- Additive bivariate convolution is commutative. -/
theorem additiveBivariateConvolution_comm (f g : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution f g = additiveBivariateConvolution g f := by
  apply bivariateCoefficientSeries_injective
  rw [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_convolution, mul_comm]

/-- The unit array is a left identity for additive bivariate convolution. -/
theorem additiveBivariateConvolution_one_left (f : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution additiveBivariateOne f = f := by
  apply bivariateCoefficientSeries_injective
  rw [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_one, one_mul]

/-- The unit array is a right identity for additive bivariate convolution. -/
theorem additiveBivariateConvolution_one_right (f : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution f additiveBivariateOne = f := by
  rw [additiveBivariateConvolution_comm, additiveBivariateConvolution_one_left]

/-- Additive bivariate convolution distributes over subtraction in the left argument. -/
theorem additiveBivariateConvolution_sub_left
    (f g h : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution (fun i j => f i j - g i j) h =
      fun i j => additiveBivariateConvolution f h i j -
        additiveBivariateConvolution g h i j := by
  apply bivariateCoefficientSeries_injective
  rw [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_sub,
    bivariateCoefficientSeries_sub,
    bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_convolution]
  ring

/-- Additive bivariate convolution distributes over subtraction in the right argument. -/
theorem additiveBivariateConvolution_sub_right
    (f g h : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution f (fun i j => g i j - h i j) =
      fun i j => additiveBivariateConvolution f g i j -
        additiveBivariateConvolution f h i j := by
  rw [additiveBivariateConvolution_comm,
    additiveBivariateConvolution_sub_left]
  funext i j
  rw [additiveBivariateConvolution_comm f g,
    additiveBivariateConvolution_comm f h]

end

end RHTower.Sieve
