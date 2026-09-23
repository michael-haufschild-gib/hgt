import GaloisForLFunctions.RHTower.CCMCompletedErrorDifferenceGate
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowDivisorTomography

/-!
# Positive variation energy of the completed error forces RH

The positive excess in the dyadic weighted-prime inequality is exactly the positive part of one
backward `log 2` difference of the completed critical-Mellin error, including its explicit
decaying endpoint value.  Consequently pointwise subpower control is unnecessary: weighted
Dirichlet energy, or weighted square energy, of only these positive variations already implies RH.
-/

open Complex Filter Function Set LSeries

noncomputable section

namespace RHTower

/-- The positive excess in the dyadic weighted-prime inequality is exactly the positive backward
variation of the completed critical-Mellin error. -/
theorem dyadicWeightedPrimeWindowPositiveExcess_eq_posPart_completedErrorBackwardDifference
    {n : ℕ} (hn : 2 ≤ n) :
    dyadicWeightedPrimeWindowPositiveExcess n =
      (criticalMellinCompletedError (Real.log n - Real.log 2) -
          criticalMellinCompletedError (Real.log n) +
          2 * (Real.sqrt 2 - 1) / Real.sqrt n)⁺ := by
  rw [dyadicWeightedPrimeWindowPositiveExcess,
    dyadicWeightedPrimeWindow_eq_floorSum,
    dyadicWeightedPrimeWindow_eq_main_add_completedErrorDifference hn]
  congr 1
  ring

/-- Positive backward completed-error variation, with the irrelevant finite prefix normalized to
the already-defined positive excess so the identity is exact at every natural index. -/
def dyadicCompletedErrorBackwardPositiveVariation (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (criticalMellinCompletedError (Real.log n - Real.log 2) -
        criticalMellinCompletedError (Real.log n) +
        2 * (Real.sqrt 2 - 1) / Real.sqrt n)⁺
  else
    dyadicWeightedPrimeWindowPositiveExcess n

theorem dyadicCompletedErrorBackwardPositiveVariation_eq_positiveExcess
    (n : ℕ) :
    dyadicCompletedErrorBackwardPositiveVariation n =
      dyadicWeightedPrimeWindowPositiveExcess n := by
  by_cases hn : 2 ≤ n
  · rw [dyadicCompletedErrorBackwardPositiveVariation, if_pos hn,
      dyadicWeightedPrimeWindowPositiveExcess_eq_posPart_completedErrorBackwardDifference hn]
  · rw [dyadicCompletedErrorBackwardPositiveVariation, if_neg hn]

/-- **Positive-variation energy gate.**  Weighted Dirichlet energy of only the positive backward
variations of the completed error, at every abscissa right of one, implies RH. -/
theorem riemannHypothesis_of_completedErrorBackwardPositiveVariationEnergy
    (henergy : ∀ epsilon : ℝ, 0 < epsilon →
      LSeriesSummable
        (fun n => ((dyadicCompletedErrorBackwardPositiveVariation n : ℝ) : ℂ))
        (((1 + epsilon : ℝ) : ℂ))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessEnergy
  intro epsilon hepsilon
  simpa only [dyadicCompletedErrorBackwardPositiveVariation_eq_positiveExcess] using
    henergy epsilon hepsilon

/-- Weighted square energy of the same positive completed-error variations is already sufficient
for RH.  This is the Hilbert-space form of the value criterion. -/
theorem riemannHypothesis_of_completedErrorBackwardPositiveVariationSquareEnergy
    (h2 : ∀ epsilon : ℝ, 0 < epsilon →
      Summable
        (realDirichletWeightedTerm
          (fun n => (dyadicCompletedErrorBackwardPositiveVariation n) ^ (2 : ℕ))
          (1 + epsilon))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessSquareEnergy
  intro epsilon hepsilon
  simpa only [dyadicCompletedErrorBackwardPositiveVariation_eq_positiveExcess] using
    h2 epsilon hepsilon

/-- **Critical positive-variation endpoint.**  Pointwise control is unnecessary: absolute
Dirichlet summability at the single critical abscissa `1` of only the positive backward
variations of the completed error already proves RH. -/
theorem riemannHypothesis_of_completedErrorBackwardPositiveVariation_summable_at_one
    (henergy : LSeriesSummable
      (fun n => ((dyadicCompletedErrorBackwardPositiveVariation n : ℝ) : ℂ)) 1) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcess_summable_at_one
  simpa only [dyadicCompletedErrorBackwardPositiveVariation_eq_positiveExcess] using henergy

end RHTower
