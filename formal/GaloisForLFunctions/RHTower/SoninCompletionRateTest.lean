import GaloisForLFunctions.RHTower.SoninCompletionSummabilityCriterion

/-!
# The rate test for a completion

The floor needs the per-scale contribution to keep up with the coupling energy.  If it falls short
by at least a fixed amount at all large scales, the sequence whose summability the floor requires
has terms bounded away from zero, so the floor fails.

This turns the remaining question into one comparison of growth rates, with no reference to how the
completion is built.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **Rate test.**  A completion whose contribution eventually falls short of the coupling energy
by a fixed positive amount cannot restore the floor. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_shortfall
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ℕ → ℝ) (hp : ∀ i, 1 < p i) (hcp : ∀ i, c < p i * a) (κ : ℕ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hshort : ∀ᶠ i in atTop, κ i + δ ≤ hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ, M ≤ soninCompletedPacketValueVar s a b c p hp κ := by
  intro hfloor
  have hzero := tendsto_min_sub_hsNormSq_of_bddBelow ha hab hbc p hp hcp κ hfloor
  have hsmall : ∀ᶠ i in atTop, -δ / 2 < min (κ i - hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) 0 :=
    hzero.eventually_const_lt (by linarith)
  obtain ⟨i, hi1, hi2⟩ := (hshort.and hsmall).exists
  have hmin := min_le_left (κ i - hsNormSq
    (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) 0
  linarith

/-- The same test read on the crossing clock. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_shortfall_clock
    (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (κ : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hshort : ∀ᶠ i in atTop, κ i + δ ≤ hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (soninCrossingClock a c i)
        (one_lt_soninCrossingClock a c i))) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c) κ :=
  not_bddBelow_soninCompletedPacketValueVar_of_shortfall ha hab hbc (soninCrossingClock a c)
    (one_lt_soninCrossingClock a c) (fun i => lt_soninCrossingClock_mul a c ha i) κ δ hδ hshort

end RHTower
