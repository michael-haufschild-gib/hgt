import GaloisForLFunctions.HTGeometry.FinitePolydiskMomentWeakConvergenceLaw

/-!
# Mixed-moment Hasse principle for finite-polydisk probability laws

The complete family of holomorphic--antiholomorphic mixed moments is a faithful observable of a
probability measure on a finite compact complex polydisk.  Thus probability laws are equivalent to
the moment profiles they realize, and every pair of distinct laws is separated by one mixed moment.

This is a measure-theoretic local--global reconstruction theorem for moment and ensemble routes.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complete mixed-moment profile of a probability law on a finite compact polydisk. -/
noncomputable def finitePolydiskProbabilityMomentProfile
    (d : Type*) [Fintype d] :
    ProbabilityMeasure (d → ClosedComplexUnitDisk) →
      (((d → ℕ) × (d → ℕ)) → ℂ) :=
  fun μ pq ↦
    ∫ x, finitePolydiskMoment pq.1 pq.2 x
      ∂(μ : Measure (d → ClosedComplexUnitDisk))

/-- Complete mixed-moment profiles faithfully encode finite-polydisk probability laws. -/
theorem finitePolydiskProbabilityMomentProfile_injective
    (d : Type*) [Fintype d] :
    Function.Injective (finitePolydiskProbabilityMomentProfile d) := by
  intro μ ν h
  apply probabilityMeasure_ext_of_finitePolydiskMoment_integral_eq μ ν
  intro p q
  exact congrFun h (p, q)

/-- Probability laws are equivalent to the complete mixed-moment profiles they realize. -/
noncomputable def finitePolydiskProbabilityMomentProfileEquivRange
    (d : Type*) [Fintype d] :
    ProbabilityMeasure (d → ClosedComplexUnitDisk) ≃
      Set.range (finitePolydiskProbabilityMomentProfile d) :=
  Equiv.ofInjective (finitePolydiskProbabilityMomentProfile d)
    (finitePolydiskProbabilityMomentProfile_injective d)

/-- Mixed-moment Hasse congruence for finite-polydisk probability laws. -/
theorem finitePolydiskProbabilityMeasure_congr_moment_hasse_iff
    {d : Type*} [Fintype d]
    (μ ν : ProbabilityMeasure (d → ClosedComplexUnitDisk)) :
    μ = ν ↔ ∀ p q : d → ℕ,
      (∫ x, finitePolydiskMoment p q x
        ∂(μ : Measure (d → ClosedComplexUnitDisk))) =
      ∫ x, finitePolydiskMoment p q x
        ∂(ν : Measure (d → ClosedComplexUnitDisk)) := by
  constructor
  · rintro rfl
    exact fun _ _ ↦ rfl
  · exact probabilityMeasure_ext_of_finitePolydiskMoment_integral_eq μ ν

/-- Distinct probability laws are detected by one mixed holomorphic-antiholomorphic moment. -/
theorem exists_finitePolydiskMoment_ne_of_probabilityMeasure_ne
    {d : Type*} [Fintype d]
    (μ ν : ProbabilityMeasure (d → ClosedComplexUnitDisk)) (hμν : μ ≠ ν) :
    ∃ p q : d → ℕ,
      (∫ x, finitePolydiskMoment p q x
        ∂(μ : Measure (d → ClosedComplexUnitDisk))) ≠
      ∫ x, finitePolydiskMoment p q x
        ∂(ν : Measure (d → ClosedComplexUnitDisk)) := by
  by_contra h
  push Not at h
  exact hμν ((finitePolydiskProbabilityMeasure_congr_moment_hasse_iff μ ν).2 h)

end

end GaloisForLFunctions.HTGeometry
