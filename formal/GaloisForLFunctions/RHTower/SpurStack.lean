/-
Full SPUR-R / AMP stack provider.

`SpurRegime` turns corrected ledger regimes into certified positive S-steps.
`SpurSMono` and `SpurMonotone` turn those steps, after a monotone or antitone
S-to-margin dressing, into a one-crossing AMP margin sequence.  This module
packages the complete terminal input: regime-certified S-readings, dressing
orientation, visibility/evenness, and the corrected reader count bound.  From
that package it exposes the transition bound, the zero-count bound, the legacy
reader input, and the exact-pair capstone.
-/
import GaloisForLFunctions.RHTower.SpurRegime

noncomputable section

namespace RHTower

/-- Terminal provider package for the proved SPUR-R / AMP reader stack. -/
structure SpurRAMPInput (S : List ℝ) (Z : ℕ) (dress : ℝ → ℝ) : Prop where
  steps : SMonoStepCerts S
  dressing : Monotone dress ∨ Antitone dress
  visible : 0 < Z
  even : Even Z
  counting_bound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map dress))

/-- Regime-certified S-steps plus a monotone/antitone dressing have at most one AMP copy/flip transition. -/
theorem copyFlipTransitions_le_one_of_spurRAMPInput {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (h : SpurRAMPInput S Z dress) :
    copyFlipTransitions (ampMarginStates (S.map dress)) ≤ 1 := by
  have hS : AdjacentStepPos S := adjacentStepPos_of_smonoStepCerts S h.steps
  rcases h.dressing with hdress | hdress
  · exact copyFlipTransitions_ampMarginStates_pairwise_le_le_one
      (List.IsChain.pairwise (isChain_map_le_of_adjacentStepPos hS hdress))
  · exact copyFlipTransitions_ampMarginStates_pairwise_ge_le_one
      (List.IsChain.pairwise (isChain_map_ge_of_adjacentStepPos hS hdress))

/-- Corrected reader counting gives `Z ≤ 2` from the full SPUR-R / AMP provider package. -/
theorem zeroCount_le_two_of_spurRAMPInput {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (h : SpurRAMPInput S Z dress) : Z ≤ 2 :=
  corrected_counting_bound_at_most_one_crossing h.counting_bound
    (copyFlipTransitions_le_one_of_spurRAMPInput h) h.even

/-- Compatibility adapter from the full SPUR-R / AMP provider to the legacy reader input. -/
theorem ampReaderInput_of_spurRAMPInput {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (h : SpurRAMPInput S Z dress) : AMPReaderInput (S.map dress) Z := by
  rcases h.dressing with hdress | hdress
  · exact ampReaderInput_of_regime_dressing_le h.steps hdress h.visible h.even h.counting_bound
  · exact ampReaderInput_of_regime_dressing_ge h.steps hdress h.visible h.even h.counting_bound

/-- Terminal exact-pair theorem for the proved SPUR-R / AMP stack. -/
theorem amp_reader_exact_pair_of_spurRAMPInput {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (h : SpurRAMPInput S Z dress) : Z = 2 :=
  even_count_eq_two_of_visible_and_le_two h.visible h.even
    (zeroCount_le_two_of_spurRAMPInput h)

end RHTower
