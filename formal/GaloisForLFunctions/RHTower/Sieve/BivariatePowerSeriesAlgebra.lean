import GaloisForLFunctions.RHTower.Sieve.BivariatePowerSeriesConvolution

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

def additiveBivariateOne (i j : ℕ) : ℝ :=
  if i = 0 ∧ j = 0 then 1 else 0

theorem bivariateCoefficientSeries_zero :
    bivariateCoefficientSeries (fun _ _ => 0) = 0 := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp

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

theorem bivariateCoefficientSeries_add (f g : ℕ → ℕ → ℝ) :
    bivariateCoefficientSeries (fun i j => f i j + g i j) =
      bivariateCoefficientSeries f + bivariateCoefficientSeries g := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp

theorem bivariateCoefficientSeries_sub (f g : ℕ → ℕ → ℝ) :
    bivariateCoefficientSeries (fun i j => f i j - g i j) =
      bivariateCoefficientSeries f - bivariateCoefficientSeries g := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp

theorem additiveBivariateConvolution_assoc (f g h : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution (additiveBivariateConvolution f g) h =
      additiveBivariateConvolution f (additiveBivariateConvolution g h) := by
  apply bivariateCoefficientSeries_injective
  rw [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_convolution,
    bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_convolution, mul_assoc]

theorem additiveBivariateConvolution_comm (f g : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution f g = additiveBivariateConvolution g f := by
  apply bivariateCoefficientSeries_injective
  rw [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_convolution, mul_comm]

theorem additiveBivariateConvolution_one_left (f : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution additiveBivariateOne f = f := by
  apply bivariateCoefficientSeries_injective
  rw [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_one, one_mul]

theorem additiveBivariateConvolution_one_right (f : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution f additiveBivariateOne = f := by
  rw [additiveBivariateConvolution_comm, additiveBivariateConvolution_one_left]

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
