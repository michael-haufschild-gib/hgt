import GaloisForLFunctions.RHTower.Zeta23SeventyPercentOrSimpleNearLine

/-!
# Simple near-line zeros required by failures of critical-line proportions

At targets `7/10`, `3/4`, and `4/5`, the forced simple off-line proportions are
respectively `HD(1) - 2/5`, `HD(1) - 1/2`, and `HD(1) - 3/5`. Restricting to
distance `A/log T` from the line costs `1/A`; the asymptotic error is arbitrary.
-/

open Zeta23

noncomputable section
namespace GaloisForLFunctions.SquareRootThreshold.Census

/-- Failure of seventy-five percent forces the `HD(1) - 1/2` near-line alternative. -/
theorem three_quarters_or_simple_offLine_near_line (A : ℝ) (hA : 0 < A) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 4 * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) ∨
        (ThmD.HD 1 - 1 / 2 - 1 / A - ε) * (Ncount T (2 * T) : ℝ) ≤
          RHTower.offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) := by
  have he : 1 + ThmD.HD 1 - 2 * (3 / 4 : ℝ) = ThmD.HD 1 - 1 / 2 := by ring
  simpa only [he] using RHTower.critical_proportion_or_simple_offLine_near_line (3 / 4) A hA

/-- Failure of eighty percent forces the `HD(1) - 3/5` near-line alternative. -/
theorem four_fifths_or_simple_offLine_near_line (A : ℝ) (hA : 0 < A) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      4 / 5 * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) ∨
        (ThmD.HD 1 - 3 / 5 - 1 / A - ε) * (Ncount T (2 * T) : ℝ) ≤
          RHTower.offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) := by
  have he : 1 + ThmD.HD 1 - 2 * (4 / 5 : ℝ) = ThmD.HD 1 - 3 / 5 := by ring
  simpa only [he] using RHTower.critical_proportion_or_simple_offLine_near_line (4 / 5) A hA

#print axioms three_quarters_or_simple_offLine_near_line
#print axioms four_fifths_or_simple_offLine_near_line

end GaloisForLFunctions.SquareRootThreshold.Census
