import GaloisForLFunctions.HTGeometry.InfiniteTorusFourierWeakConvergenceLaw

/-!
# Fourier Hasse principle for countable product-torus probability laws

Finite-support integer characters form a faithful observable family on an arbitrary countable
product of additive circles.  Complete global probability laws are reconstructed from these finite
cylinder frequencies, and one finite-support character detects every pair of distinct laws.

This is an infinite-dimensional harmonic local--global principle: every individual probe remains
finitely supported despite the global carrier having countably many coordinates.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complete finite-support Fourier profile of a law on a countable product torus. -/
noncomputable def infiniteTorusProbabilityFourierProfile
    (I : Type*) [Countable I] :
    ProbabilityMeasure (I → UnitAddCircle) → ((I →₀ ℤ) → ℂ) :=
  fun μ n ↦
    ∫ x, infiniteTorusFourier n x ∂(μ : Measure (I → UnitAddCircle))

/-- Finite-support Fourier profiles faithfully encode countable-product-torus laws. -/
theorem infiniteTorusProbabilityFourierProfile_injective
    (I : Type*) [Countable I] :
    Function.Injective (infiniteTorusProbabilityFourierProfile I) := by
  intro μ ν h
  exact probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq μ ν
    (fun n ↦ congrFun h n)

/-- Product-torus laws are equivalent to the finite-support Fourier profiles they realize. -/
noncomputable def infiniteTorusProbabilityFourierProfileEquivRange
    (I : Type*) [Countable I] :
    ProbabilityMeasure (I → UnitAddCircle) ≃
      Set.range (infiniteTorusProbabilityFourierProfile I) :=
  Equiv.ofInjective (infiniteTorusProbabilityFourierProfile I)
    (infiniteTorusProbabilityFourierProfile_injective I)

/-- Fourier Hasse congruence for countable product-torus probability laws. -/
theorem infiniteTorusProbabilityMeasure_congr_fourier_hasse_iff
    {I : Type*} [Countable I]
    (μ ν : ProbabilityMeasure (I → UnitAddCircle)) :
    μ = ν ↔ ∀ n : I →₀ ℤ,
      (∫ x, infiniteTorusFourier n x
        ∂(μ : Measure (I → UnitAddCircle))) =
      ∫ x, infiniteTorusFourier n x
        ∂(ν : Measure (I → UnitAddCircle)) := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · exact probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq μ ν

/-- Distinct product-torus laws differ at one finite-support Fourier character. -/
theorem exists_infiniteTorusFourier_ne_of_probabilityMeasure_ne
    {I : Type*} [Countable I]
    (μ ν : ProbabilityMeasure (I → UnitAddCircle)) (hμν : μ ≠ ν) :
    ∃ n : I →₀ ℤ,
      (∫ x, infiniteTorusFourier n x
        ∂(μ : Measure (I → UnitAddCircle))) ≠
      ∫ x, infiniteTorusFourier n x
        ∂(ν : Measure (I → UnitAddCircle)) := by
  by_contra h
  push Not at h
  exact hμν ((infiniteTorusProbabilityMeasure_congr_fourier_hasse_iff μ ν).2 h)

end

end GaloisForLFunctions.HTGeometry
