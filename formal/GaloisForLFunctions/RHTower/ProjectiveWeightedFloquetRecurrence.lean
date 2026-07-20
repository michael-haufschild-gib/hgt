import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherenceMinimax

/-!
# Weighted pure-state Floquet recurrence

For a pure state with spectral probabilities `w`, the return fidelity under a
diagonal Floquet operator is the square of the weighted phase amplitude.  This
file transfers the projective water-entropy minimax theorem to that physical
language without randomness or a generic-spectrum assumption.
-/

noncomputable section

namespace RHTower

/-- Pure-state return amplitude of a finite diagonal Floquet packet. -/
def weightedFloquetReturnAmplitude {d : ℕ} (w : Fin d → ℝ)
    (omega : Fin d → ℝ) (n : ℕ) : ℂ :=
  ∑ j, (w j : ℂ) * Complex.exp
    (Complex.I * ((((n : ℝ) * omega j : ℝ) : ℂ)))

/-- Pure-state return fidelity of a finite diagonal Floquet packet. -/
def weightedFloquetReturnFidelity {d : ℕ} (w : Fin d → ℝ)
    (omega : Fin d → ℝ) (n : ℕ) : ℝ :=
  ‖weightedFloquetReturnAmplitude w omega n‖ ^ 2

/-- A universal fidelity deadline at amplitude defect `eta`. -/
def IsUniversalWeightedFloquetFidelityDeadline {d : ℕ}
    (w : Fin d → ℝ) (eta : ℝ) (N : ℕ) : Prop :=
  ∀ omega : Fin d → ℝ, ∃ n : ℕ, 0 < n ∧ n ≤ N ∧
    (1 - eta) ^ 2 ≤ weightedFloquetReturnFidelity w omega n

/-- Fidelity recurrence and projective amplitude recurrence are exactly the
same deadline problem when the target amplitude is nonnegative. -/
theorem isUniversalWeightedFloquetFidelityDeadline_iff
    {d N : ℕ} (w : Fin d → ℝ) {eta : ℝ} (heta1 : eta ≤ 1) :
    IsUniversalWeightedFloquetFidelityDeadline w eta N ↔
      IsUniversalProjectiveWeightedCoherenceDeadline w eta N := by
  have htarget : 0 ≤ 1 - eta := sub_nonneg.mpr heta1
  constructor
  · intro h omega
    obtain ⟨n, hn0, hnN, hn⟩ := h omega
    refine ⟨n, hn0, hnN, ?_⟩
    change (1 - eta) ^ 2 ≤
      ‖∑ j, (w j : ℂ) * Complex.exp
        (Complex.I * ((((n : ℝ) * omega j : ℝ) : ℂ)))‖ ^ 2 at hn
    exact (sq_le_sq₀ htarget (norm_nonneg _)).mp hn
  · intro h omega
    obtain ⟨n, hn0, hnN, hn⟩ := h omega
    refine ⟨n, hn0, hnN, ?_⟩
    change (1 - eta) ^ 2 ≤
      ‖∑ j, (w j : ℂ) * Complex.exp
        (Complex.I * ((((n : ℝ) * omega j : ℝ) : ℂ)))‖ ^ 2
    exact (sq_le_sq₀ htarget (norm_nonneg _)).mpr hn

/-- Least universal pure-state Floquet fidelity deadline. -/
noncomputable def universalWeightedFloquetFidelityRecurrenceTime
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) : ℕ :=
  universalProjectiveWeightedCoherenceTime
    hd w hw hmass eta heta0 heta1

theorem universalWeightedFloquetFidelityRecurrenceTime_isDeadline
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    IsUniversalWeightedFloquetFidelityDeadline w eta
      (universalWeightedFloquetFidelityRecurrenceTime
        hd w hw hmass eta heta0 heta1) := by
  apply (isUniversalWeightedFloquetFidelityDeadline_iff w heta1).mpr
  exact universalProjectiveWeightedCoherenceTime_isDeadline
    hd w hw hmass eta heta0 heta1

theorem universalWeightedFloquetFidelityRecurrenceTime_le_of_deadline
    {d N : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hdeadline : IsUniversalWeightedFloquetFidelityDeadline w eta N) :
    universalWeightedFloquetFidelityRecurrenceTime
      hd w hw hmass eta heta0 heta1 ≤ N := by
  apply universalProjectiveWeightedCoherenceTime_le_of_deadline
    hd w hw hmass eta heta0 heta1
  exact (isUniversalWeightedFloquetFidelityDeadline_iff w heta1).mp hdeadline

/-- Exact minimax water-entropy law for weighted pure-state Floquet
recurrence. -/
theorem universalWeightedFloquetFidelityRecurrenceTime_entropySandwich
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    projectiveCanonicalWaterEntropyMinimum (by omega) w eta -
        (Real.pi / 4) * (d - 1 : ℕ) - Real.log (2 * (d : ℝ)) <
      Real.log (universalWeightedFloquetFidelityRecurrenceTime
        hd w hw hmass eta heta0 heta1 : ℝ) ∧
    Real.log (universalWeightedFloquetFidelityRecurrenceTime
        hd w hw hmass eta heta0 heta1 : ℝ) ≤
      projectiveCanonicalWaterEntropyMinimum (by omega) w eta +
        (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
  simpa only [universalWeightedFloquetFidelityRecurrenceTime] using
    universalProjectiveWeightedCoherenceTime_entropySandwich
      hd w hw hmass eta heta0 heta1

end RHTower
