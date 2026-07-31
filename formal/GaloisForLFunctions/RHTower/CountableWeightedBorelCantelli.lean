import GaloisForLFunctions.RHTower.SummableWeightedInfinitePhaseQuantile
import GaloisForLFunctions.HTGeometry.FinitePiProductSummability
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

/--
Reusable Gaussian-budget closure. A polynomial prefactor cannot obstruct
Borel--Cantelli when the early-hit probability has a strictly negative
quadratic exponent.
-/
theorem
    ae_eventually_not_countableTorusWeightedCoherenceHitUnion_of_polynomialGaussian
    (ν : Measure (ℕ → UnitAddCircle)) [IsFiniteMeasure ν]
    (p : ℕ → ℝ) (N : ℕ → ℕ) (η : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (A : ℕ)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hmeasure : ∀ k,
      ν.real
          (countableTorusWeightedCoherenceHitUnion p (N k) (η k)) ≤
        C * (1 + (k : ℝ)) ^ A *
          Real.exp (-sigma * (k : ℝ) ^ 2)) :
    ∀ᵐ x ∂ν, ∀ᶠ k in Filter.atTop,
      x ∉ countableTorusWeightedCoherenceHitUnion p (N k) (η k) := by
  let budget : ℕ → NNReal := fun k =>
    ⟨C * (1 + (k : ℝ)) ^ A *
        Real.exp (-sigma * (k : ℝ) ^ 2), by positivity⟩
  apply
    ae_eventually_not_countableTorusWeightedCoherenceHitUnion_of_le
      ν p N η (fun k => (budget k : ENNReal))
  · intro k
    apply (ENNReal.toReal_le_toReal
      (by finiteness : ν
        (countableTorusWeightedCoherenceHitUnion p (N k) (η k)) ≠ ⊤)
      ENNReal.coe_ne_top).mp
    change ν.real
        (countableTorusWeightedCoherenceHitUnion p (N k) (η k)) ≤
      C * (1 + (k : ℝ)) ^ A *
        Real.exp (-sigma * (k : ℝ) ^ 2)
    exact hmeasure k
  · rw [ENNReal.tsum_coe_ne_top_iff_summable_coe]
    change Summable (fun k : ℕ =>
      C * (1 + (k : ℝ)) ^ A *
        Real.exp (-sigma * (k : ℝ) ^ 2))
    simpa only [mul_assoc] using
      (GaloisForLFunctions.summable_one_add_pow_mul_exp_neg_nat_sq
        A hsigma).mul_left C

end RHTower
