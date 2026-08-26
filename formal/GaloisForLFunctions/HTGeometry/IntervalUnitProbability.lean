import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Uniform probability on `[1,2]`

Lightweight home for the normalized interval law shared by product-probability constructions.
-/

open MeasureTheory Set

namespace GaloisForLFunctions

noncomputable section

/-- Lebesgue measure restricted to `[1,2]`, whose interval length is one. -/
def intervalUnitProbability : Measure ℝ :=
  volume.restrict (Set.Icc 1 2)

instance : IsProbabilityMeasure intervalUnitProbability where
  measure_univ := by
    rw [intervalUnitProbability, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc]
    norm_num

end

end GaloisForLFunctions
