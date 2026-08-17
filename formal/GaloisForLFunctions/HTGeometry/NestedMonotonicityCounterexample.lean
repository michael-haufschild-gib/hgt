import GaloisForLFunctions.HTGeometry.NestedMonotonicityUpper

/-!
# Literal all-pairs monotonicity fails inside the laboratory window
-/

open Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- At two increasing laboratory times separated by only `10⁻⁶`, exact operator-norm circuit
complexity decreases. -/
theorem monotonicityCounter_strict_complexity_reversal :
    nestedOperatorTwoGateComplexity monotonicityCounterLength
        monotonicityCounterEpsilon monotonicityCounterLateTime <
      nestedOperatorTwoGateComplexity monotonicityCounterLength
        monotonicityCounterEpsilon monotonicityCounterEarlyTime := by
  exact lt_of_lt_of_le
    (lt_of_le_of_lt monotonicityCounterLate_complexity_upper (by norm_num))
    monotonicityCounterEarly_complexity_lower

/-- Literal all-pairs monotonicity is false even when both times lie in the certified laboratory
window. -/
theorem nestedOperatorTwoGateComplexity_not_monotoneOn_laboratoryWindow :
    ¬ MonotoneOn
      (nestedOperatorTwoGateComplexity monotonicityCounterLength
        monotonicityCounterEpsilon)
      (Icc (1024 * Real.pi * monotonicityCounterEpsilon)
        (monotonicityCounterEpsilon * monotonicityCounterLength / 2)) := by
  intro hmono
  rcases monotonicityCounterWindow with ⟨hearlyMin, htimes, hlateMax⟩
  have hearlyMem : monotonicityCounterEarlyTime ∈
      Icc (1024 * Real.pi * monotonicityCounterEpsilon)
        (monotonicityCounterEpsilon * monotonicityCounterLength / 2) :=
    ⟨hearlyMin, le_trans htimes.le hlateMax⟩
  have hlateMem : monotonicityCounterLateTime ∈
      Icc (1024 * Real.pi * monotonicityCounterEpsilon)
        (monotonicityCounterEpsilon * monotonicityCounterLength / 2) :=
    ⟨le_trans hearlyMin htimes.le, hlateMax⟩
  have hle := hmono hearlyMem hlateMem htimes.le
  exact (not_le_of_gt monotonicityCounter_strict_complexity_reversal) hle

/-- Existential all-pairs formulation: there are increasing times in the laboratory window at
which exact complexity strictly drops. -/
theorem exists_laboratory_complexity_drop :
    ∃ s t : ℝ,
      1024 * Real.pi * monotonicityCounterEpsilon ≤ s ∧
      s < t ∧
      t ≤ monotonicityCounterEpsilon * monotonicityCounterLength / 2 ∧
      nestedOperatorTwoGateComplexity monotonicityCounterLength
          monotonicityCounterEpsilon t <
        nestedOperatorTwoGateComplexity monotonicityCounterLength
          monotonicityCounterEpsilon s := by
  exact ⟨monotonicityCounterEarlyTime, monotonicityCounterLateTime,
    monotonicityCounterWindow.1, monotonicityCounterWindow.2.1,
    monotonicityCounterWindow.2.2, monotonicityCounter_strict_complexity_reversal⟩

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
