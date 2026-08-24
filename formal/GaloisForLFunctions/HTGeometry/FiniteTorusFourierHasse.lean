import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw

/-!
# Fourier Hasse principle for finite-torus probability laws

All integer-frequency character integrals form a faithful profile of a probability measure on a
finite additive torus.  Thus phase laws are equivalent to their realized Fourier profiles, and one
frequency detects every pair of distinct laws.

This is a finite-dimensional harmonic local--global principle for phase-ensemble routes.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complete Fourier profile of a probability law on a finite additive torus. -/
noncomputable def finiteTorusProbabilityFourierProfile
    (d : Type*) [Fintype d] :
    ProbabilityMeasure (UnitAddTorus d) → ((d → ℤ) → ℂ) :=
  fun μ n ↦
    ∫ x, UnitAddTorus.mFourier n x ∂(μ : Measure (UnitAddTorus d))

/-- Finite-torus Fourier profiles faithfully encode probability laws. -/
theorem finiteTorusProbabilityFourierProfile_injective
    (d : Type*) [Fintype d] :
    Function.Injective (finiteTorusProbabilityFourierProfile d) := by
  intro μ ν h
  exact probabilityMeasure_ext_of_mFourier_integral_eq μ ν (fun n ↦ congrFun h n)

/-- Finite-torus probability laws are equivalent to realized Fourier profiles. -/
noncomputable def finiteTorusProbabilityFourierProfileEquivRange
    (d : Type*) [Fintype d] :
    ProbabilityMeasure (UnitAddTorus d) ≃
      Set.range (finiteTorusProbabilityFourierProfile d) :=
  Equiv.ofInjective (finiteTorusProbabilityFourierProfile d)
    (finiteTorusProbabilityFourierProfile_injective d)

/-- Fourier Hasse congruence for finite-torus probability laws. -/
theorem finiteTorusProbabilityMeasure_congr_fourier_hasse_iff
    {d : Type*} [Fintype d]
    (μ ν : ProbabilityMeasure (UnitAddTorus d)) :
    μ = ν ↔ ∀ n : d → ℤ,
      (∫ x, UnitAddTorus.mFourier n x
        ∂(μ : Measure (UnitAddTorus d))) =
      ∫ x, UnitAddTorus.mFourier n x
        ∂(ν : Measure (UnitAddTorus d)) := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · exact probabilityMeasure_ext_of_mFourier_integral_eq μ ν

/-- Distinct finite-torus probability laws differ at one Fourier character. -/
theorem exists_finiteTorusFourier_ne_of_probabilityMeasure_ne
    {d : Type*} [Fintype d]
    (μ ν : ProbabilityMeasure (UnitAddTorus d)) (hμν : μ ≠ ν) :
    ∃ n : d → ℤ,
      (∫ x, UnitAddTorus.mFourier n x
        ∂(μ : Measure (UnitAddTorus d))) ≠
      ∫ x, UnitAddTorus.mFourier n x
        ∂(ν : Measure (UnitAddTorus d)) := by
  by_contra h
  push Not at h
  exact hμν ((finiteTorusProbabilityMeasure_congr_fourier_hasse_iff μ ν).2 h)

end

end GaloisForLFunctions.HTGeometry
