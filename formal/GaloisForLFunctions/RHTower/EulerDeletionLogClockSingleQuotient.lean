import GaloisForLFunctions.RHTower.EulerDeletionLogClockConditionalApproximation
import GaloisForLFunctions.RHTower.EulerDeletionPredictableDriftFirstTail

/-!
# One signed quotient carries the logarithmic EDQ obstruction

The moving low-clock projection of the drift differs from the projection of
the literal Möbius source only by a uniformly bounded martingale. The latter
is one periodic field whose pointwise coordinates are the complete paired
Möbius quotients. No coefficientwise absolute-value estimate is used.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory

namespace RHTower.DeletionResidueMartingale

/-- The source's single logarithmic-clock conditional expectation. -/
def logClockSourceProjection (N : ℕ) : Lp ℝ 2 cellMeasure :=
  (historySpace (min (logarithmicClockThreshold N) N)).starProjection
    (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)

/-- Its coordinates retain the complete signed paired Möbius quotient. -/
theorem logClockSourceProjection_apply (N j : ℕ) :
    logClockSourceProjection N j =
      pairedMoebiusQuotient N (min (logarithmicClockThreshold N) N)
        (j % clock (min (logarithmicClockThreshold N) N)) := by
  exact historyProjection_source_apply_eq_pairedMoebiusQuotient N
    (min (logarithmicClockThreshold N) N) j

private theorem norm_add_sq_le_two (x y : Lp ℝ 2 cellMeasure) :
    ‖x + y‖ ^ (2 : ℕ) ≤ 2 * ‖x‖ ^ (2 : ℕ) + 2 * ‖y‖ ^ (2 : ℕ) := by
  have hnorm := norm_add_le x y
  have hsq := (sq_le_sq₀ (norm_nonneg (x + y))
    (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr hnorm
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem logClock_martingale_projection_sq_le_two (N : ℕ) :
    ‖(historySpace (min (logarithmicClockThreshold N) N)).starProjection
      (martingalePart N)‖ ^ (2 : ℕ) ≤ 2 := by
  have h := (historySpace (min (logarithmicClockThreshold N) N)).norm_starProjection_apply_le
    (martingalePart N)
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (norm_nonneg (martingalePart N))).mpr h
  exact hsq.trans (martingalePart_sq_le_two N)

private theorem logClockSourceProjection_eq_martingale_add_drift (N : ℕ) :
    logClockSourceProjection N =
      (historySpace (min (logarithmicClockThreshold N) N)).starProjection
        (martingalePart N) +
      (historySpace (min (logarithmicClockThreshold N) N)).starProjection
        (predictableDrift N) := by
  unfold logClockSourceProjection
  rw [source_eq_martingale_add_drift, map_add]

/-- The single signed quotient energy is at most twice the low-clock drift
energy, up to the bounded innovation budget. -/
theorem logClockSourceProjection_sq_le_two_lowClock_add_four (N : ℕ) :
    ‖logClockSourceProjection N‖ ^ (2 : ℕ) ≤
      2 * lowClockProducerEnergy N + 4 := by
  rw [logClockSourceProjection_eq_martingale_add_drift]
  have h := norm_add_sq_le_two
    ((historySpace (min (logarithmicClockThreshold N) N)).starProjection
      (martingalePart N))
    ((historySpace (min (logarithmicClockThreshold N) N)).starProjection
      (predictableDrift N))
  rw [lowClockProducerEnergy_eq_historyProjection_norm_sq]
  linarith [logClock_martingale_projection_sq_le_two N]

/-- Conversely, all possibly unbounded low-clock drift energy is carried by
this one signed quotient, again up to the bounded innovation budget. -/
theorem lowClockProducerEnergy_le_two_logClockSourceProjection_sq_add_four (N : ℕ) :
    lowClockProducerEnergy N ≤ 2 * ‖logClockSourceProjection N‖ ^ (2 : ℕ) + 4 := by
  let P := (historySpace (min (logarithmicClockThreshold N) N)).starProjection
  have hsource := logClockSourceProjection_eq_martingale_add_drift N
  have hrewrite : P (predictableDrift N) =
      logClockSourceProjection N + -(P (martingalePart N)) := by
    change logClockSourceProjection N = P (martingalePart N) + P (predictableDrift N)
      at hsource
    rw [hsource]
    abel
  rw [lowClockProducerEnergy_eq_historyProjection_norm_sq, hrewrite]
  have h := norm_add_sq_le_two (logClockSourceProjection N) (-(P (martingalePart N)))
  simpa only [norm_neg] using
    le_trans h (by
      have hm : ‖-P (martingalePart N)‖ ^ (2 : ℕ) ≤ 2 := by
        simpa only [norm_neg] using logClock_martingale_projection_sq_le_two N
      linarith)

/-- Full predictable-drift energy reduces to one signed paired-source
quotient, a bounded innovation term, and a vanishing high-clock error. -/
theorem predictableDrift_sq_le_two_logClockSourceProjection_sq_add_error (N : ℕ) :
    ‖predictableDrift N‖ ^ (2 : ℕ) ≤
      2 * ‖logClockSourceProjection N‖ ^ (2 : ℕ) + 4 + 110 / ((N : ℝ) + 1) := by
  have hlow := lowClockProducerEnergy_le_two_logClockSourceProjection_sq_add_four N
  have hhigh := predictableDrift_logarithmic_highClock_energy_le N
  rw [predictableDrift_norm_sq_eq_lowClock_add_highClock]
  simpa only [Nat.cast_add, Nat.cast_one] using add_le_add hlow hhigh

end RHTower.DeletionResidueMartingale
