import GaloisForLFunctions.RHTower.SummableWeightedInfinitePhaseQuantile
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Borel--Cantelli lift for countable weighted recurrence

Summable scale-wise early-hit probabilities imply that almost every
countable phase packet eventually avoids every proposed premature
recurrence deadline. Independence across clocks or scales is not required.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace RHTower

/--
First Borel--Cantelli reduction for countable weighted recurrence. If the
measures of the early-hit events are summable, almost every phase packet
avoids those early deadlines at all sufficiently fine scales.
-/
theorem ae_eventually_not_countableTorusWeightedCoherenceHitUnion
    (ν : Measure (ℕ → UnitAddCircle))
    (p : ℕ → ℝ) (N : ℕ → ℕ) (η : ℕ → ℝ)
    (hsum :
      (∑' k, ν
        (countableTorusWeightedCoherenceHitUnion p (N k) (η k))) ≠ ∞) :
    ∀ᵐ x ∂ν, ∀ᶠ k in Filter.atTop,
      x ∉ countableTorusWeightedCoherenceHitUnion p (N k) (η k) := by
  exact ae_eventually_notMem hsum

/--
Dominated Borel--Cantelli form. Any summable explicit ENNReal budget for
the scale-wise early-hit events yields eventual almost-sure avoidance.
-/
theorem
    ae_eventually_not_countableTorusWeightedCoherenceHitUnion_of_le
    (ν : Measure (ℕ → UnitAddCircle))
    (p : ℕ → ℝ) (N : ℕ → ℕ) (η : ℕ → ℝ)
    (budget : ℕ → ENNReal)
    (hmeasure : ∀ k,
      ν (countableTorusWeightedCoherenceHitUnion p (N k) (η k)) ≤
        budget k)
    (hbudget : (∑' k, budget k) ≠ ∞) :
    ∀ᵐ x ∂ν, ∀ᶠ k in Filter.atTop,
      x ∉ countableTorusWeightedCoherenceHitUnion p (N k) (η k) := by
  apply ae_eventually_not_countableTorusWeightedCoherenceHitUnion
  apply ne_top_of_le_ne_top hbudget
  exact ENNReal.tsum_le_tsum hmeasure

end RHTower
