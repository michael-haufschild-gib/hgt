import GaloisForLFunctions.RHTower.EulerDeletionLogClockProducerReduction
import GaloisForLFunctions.RHTower.EulerDeletionPrimePowerCanonicalResolventEnergy
import GaloisForLFunctions.RHTower.EulerDeletionPredictableDriftFirstTail

/-!
# Signed prime-power carrier of the logarithmic EDQ producer

The high-clock estimate removes all but logarithmically many chronological
steps. This file identifies the *remaining* energy with its literal signed
Möbius beta-resolvent fibres. The first-tail theorem then forces a
fixed-start Möbius window below this same carrier, up to a vanishing error.
No bound on the signed low-clock carrier is asserted.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace RHTower.DeletionResidueMartingale

/-- Exact low-clock arithmetic producer: only prime-power steps survive, and
each fibre retains the entire signed source and its local innovation. -/
theorem lowClockProducerEnergy_eq_primePower_canonicalBetaResolvent_energy (N : ℕ) :
    lowClockProducerEnergy N =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ (2 : ℕ) +
        ∑ l ∈ (range (min (logarithmicClockThreshold N) N)).filter
            (fun l => IsPrimePow (l + 1)),
          ∑ r ∈ range (clock (l + 1)),
            cellMeasure.real (historyFibre (l + 1) r) *
              (canonicalBetaResolvent N (l + 1) r -
                canonicalBetaResolvent N l (r % clock l) - signedInnovation l r) ^ (2 : ℕ) := by
  unfold lowClockProducerEnergy
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hp : IsPrimePow (l + 1)
  · rw [if_pos hp]
    exact historyLayer_predictableDrift_norm_sq_eq_canonicalBetaResolvent_fibre_energy
      l N (lt_of_lt_of_le (Finset.mem_range.mp hl) (min_le_right _ _))
  · rw [if_neg hp, historyLayer_predictableDrift_eq_zero_of_not_isPrimePow l N hp]
    simp

/-- The first literal complementary Möbius window is already an obligation on
the signed prime-power low-clock carrier, with an explicit vanishing high-clock
remainder. -/
theorem incrementEnergy_le_lowClockProducer_add_vanishing (N : ℕ) :
    DeletionFirstTail.incrementEnergy N ≤
      24 * lowClockProducerEnergy N + 2640 / ((N : ℝ) + 1) + 60 := by
  have hfirst :=
    DeletionPredictableFirstTail.incrementEnergy_le_twentyfour_drift_sq_add_sixty N
  have hhigh := predictableDrift_logarithmic_highClock_energy_le N
  rw [predictableDrift_norm_sq_eq_lowClock_add_highClock] at hfirst
  simp only [Nat.cast_add, Nat.cast_one] at hhigh
  calc
    _ ≤ 24 * (lowClockProducerEnergy N +
          ∑ l ∈ Ico (logarithmicClockThreshold N) N,
            ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ)) + 60 := hfirst
    _ ≤ 24 * (lowClockProducerEnergy N + 110 / ((N : ℝ) + 1)) + 60 := by
      gcongr
    _ = _ := by ring

end RHTower.DeletionResidueMartingale
