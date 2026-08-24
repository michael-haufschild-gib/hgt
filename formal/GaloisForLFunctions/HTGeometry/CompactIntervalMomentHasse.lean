import GaloisForLFunctions.HTGeometry.CompactMomentWeakConvergence

/-!
# Hausdorff-moment Hasse principle on compact intervals

A nonempty compact real interval is packaged intrinsically.  Every probability law on it is
determined by the sequence of power moments, is equivalent to the moment profiles actually
realized, and differs from any other law at one finite degree.

This is ensemble-level local--global reconstruction for moment and spectral-measure routes.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Intrinsic nonempty compact real interval. -/
structure CompactIntervalDatum where
  lower : ℝ
  upper : ℝ
  lower_le_upper : lower ≤ upper

namespace CompactIntervalDatum

instance (I : CompactIntervalDatum) : Nonempty (Icc I.lower I.upper) :=
  ⟨⟨I.lower, le_rfl, I.lower_le_upper⟩⟩

/-- Complete Hausdorff moment profile of a probability law on the interval. -/
noncomputable def probabilityMomentProfile (I : CompactIntervalDatum) :
    ProbabilityMeasure (Icc I.lower I.upper) → (ℕ → ℝ) :=
  fun μ k ↦ ∫ y, ((y : ℝ) ^ k) ∂(μ : Measure (Icc I.lower I.upper))

/-- Hausdorff moment profiles faithfully encode compact-interval probability laws. -/
theorem probabilityMomentProfile_injective (I : CompactIntervalDatum) :
    Function.Injective I.probabilityMomentProfile := by
  intro μ ν h
  exact probabilityMeasure_ext_of_integral_pow_eq μ ν (fun k ↦ congrFun h k)

/-- Interval probability laws are equivalent to the moment profiles they realize. -/
noncomputable def probabilityMomentProfileEquivRange (I : CompactIntervalDatum) :
    ProbabilityMeasure (Icc I.lower I.upper) ≃ Set.range I.probabilityMomentProfile :=
  Equiv.ofInjective I.probabilityMomentProfile I.probabilityMomentProfile_injective

/-- Hausdorff-moment Hasse congruence for compact-interval probability laws. -/
theorem probabilityMeasure_congr_moment_hasse_iff
    (I : CompactIntervalDatum)
    (μ ν : ProbabilityMeasure (Icc I.lower I.upper)) :
    μ = ν ↔ ∀ k : ℕ,
      (∫ y, ((y : ℝ) ^ k) ∂(μ : Measure (Icc I.lower I.upper))) =
        ∫ y, ((y : ℝ) ^ k) ∂(ν : Measure (Icc I.lower I.upper)) := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · exact probabilityMeasure_ext_of_integral_pow_eq μ ν

/-- Distinct compact-interval laws are detected by one power moment. -/
theorem exists_moment_ne_of_probabilityMeasure_ne
    (I : CompactIntervalDatum)
    (μ ν : ProbabilityMeasure (Icc I.lower I.upper)) (hμν : μ ≠ ν) :
    ∃ k : ℕ,
      (∫ y, ((y : ℝ) ^ k) ∂(μ : Measure (Icc I.lower I.upper))) ≠
        ∫ y, ((y : ℝ) ^ k) ∂(ν : Measure (Icc I.lower I.upper)) := by
  by_contra h
  push Not at h
  exact hμν ((I.probabilityMeasure_congr_moment_hasse_iff μ ν).2 h)

end CompactIntervalDatum

end

end GaloisForLFunctions.HTGeometry
