import GaloisForLFunctions.RHTower.Sieve.SelbergPrincipalPrimePowerValues
import Mathlib.RingTheory.PowerSeries.Basic

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

def bivariateCoefficientSeries (f : ℕ → ℕ → ℝ) : PowerSeries (PowerSeries ℝ) :=
  PowerSeries.mk (fun i => PowerSeries.mk (f i))

@[simp] theorem coeff_bivariateCoefficientSeries (f : ℕ → ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (bivariateCoefficientSeries f)) = f i j := by
  simp [bivariateCoefficientSeries]

def additiveBivariateConvolution (f g : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
    f a b * g (i - a) (j - b)

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

theorem bivariateCoefficientSeries_convolution (f g : ℕ → ℕ → ℝ) :
    bivariateCoefficientSeries (additiveBivariateConvolution f g) =
      bivariateCoefficientSeries f * bivariateCoefficientSeries g := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  rw [coeff_bivariateCoefficientSeries, coeff_mul_bivariateCoefficientSeries]

theorem bivariateCoefficientSeries_injective :
    Function.Injective bivariateCoefficientSeries := by
  intro f g h
  funext i j
  have hc := congrArg (fun F => PowerSeries.coeff j (PowerSeries.coeff i F)) h
  simpa using hc

end

end RHTower.Sieve
