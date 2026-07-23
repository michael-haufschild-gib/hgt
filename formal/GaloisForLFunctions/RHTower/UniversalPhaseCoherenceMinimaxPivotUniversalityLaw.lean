import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceHalfEntropyLaw
import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceMinimax

/-!
# Universal phase-coherence minimax-pivot law

The least universal deadline for near-unit phase amplitude is unchanged when every witness is
required to carry a packet pivot with controlled total squared chordal dispersion. Consequently
the exact minimax entropy clock, not merely the Dirichlet ceiling, controls phase clustering.
-/

open scoped BigOperators RealInnerProductSpace

namespace RHTower

noncomputable section

/-- A universal deadline whose coherent clock also carries a phase pivot with the sharp centroid
dispersion bound at the recurrence defect. -/
def IsUniversalPhaseCoherencePivotDeadline
    (d Q N : ℕ) : Prop :=
  ∀ ω : Fin d → ℝ, ∃ n : ℕ, ∃ k : Fin d,
    0 < n ∧ n ≤ N ∧
      1 - recurrencePhaseDefect Q ≤ ‖phaseClockAmplitude ω n‖ ∧
      ∑ j : Fin d,
          ‖Complex.exp (Complex.I * (((n : ℝ) * ω j : ℝ) : ℂ)) -
            Complex.exp (Complex.I * (((n : ℝ) * ω k : ℝ) : ℂ))‖ ^ 2 ≤
        4 * recurrencePhaseDefect Q * (d : ℝ)

/-- Adding the centroid-pivot certificate does not change the class of universal deadlines. -/
theorem isUniversalPhaseCoherencePivotDeadline_iff
    {d Q N : ℕ} (hd : 0 < d) :
    IsUniversalPhaseCoherencePivotDeadline d Q N ↔
      IsUniversalPhaseCoherenceDeadline d (recurrencePhaseDefect Q) N := by
  constructor
  · intro hpivot ω
    obtain ⟨n, k, hnpos, hnN, hcoh, hk⟩ := hpivot ω
    exact ⟨n, hnpos, hnN, hcoh⟩
  · intro hdeadline ω
    letI : NeZero d := ⟨hd.ne'⟩
    obtain ⟨n, hnpos, hnN, hcoh⟩ := hdeadline ω
    let phase : Fin d → ℂ := fun i =>
      Complex.exp (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))
    have hphase : ∀ i, ‖phase i‖ = 1 := by
      intro i
      rw [show phase i = Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) by rfl, Complex.norm_exp]
      simp
    have hcoh' :
        1 - recurrencePhaseDefect Q ≤ ‖equalPhaseAmplitude phase‖ := by
      rw [← phaseClockAmplitude_eq_equalPhaseAmplitude ω n]
      exact hcoh
    obtain ⟨k, hk⟩ :=
      exists_phasePivot_sum_norm_sub_sq_le phase hphase hcoh'
    refine ⟨n, k, hnpos, hnN, hcoh, ?_⟩
    simpa only [phase, Fintype.card_fin] using hk

/-- **Universal minimax-pivot entropy law.**  The exact minimax coherence time is the least
deadline even after every clock must carry a controlled phase pivot, and it retains the full
dimension--resolution entropy sandwich. -/
theorem universalPhaseCoherence_minimaxPivotEntropyUniversality
    {d Q : ℕ} (hd : 0 < d) :
    IsUniversalPhaseCoherencePivotDeadline d Q
        (universalPhaseCoherenceTime d Q hd) ∧
      (∀ N, IsUniversalPhaseCoherencePivotDeadline d Q N →
        universalPhaseCoherenceTime d Q hd ≤ N) ∧
      (((d - 1 : ℕ) : ℝ) * Real.log (Q + 1 : ℝ) -
            ((d - 1 : ℕ) : ℝ) * Real.log phaseCoherenceResolutionConstant -
              (d : ℝ) / 2 - Real.log (2 * (d : ℝ)) <
          Real.log (universalPhaseCoherenceTime d Q hd : ℝ) ∧
        Real.log (universalPhaseCoherenceTime d Q hd : ℝ) ≤
          (d : ℝ) * Real.log (Q + 1 : ℝ)) := by
  have hpivot : IsUniversalPhaseCoherencePivotDeadline d Q
      (universalPhaseCoherenceTime d Q hd) :=
    (isUniversalPhaseCoherencePivotDeadline_iff hd).2
      (universalPhaseCoherenceTime_isDeadline d Q hd)
  have hminimal : ∀ N, IsUniversalPhaseCoherencePivotDeadline d Q N →
      universalPhaseCoherenceTime d Q hd ≤ N := by
    intro N hN
    have hdeadline : IsUniversalPhaseCoherenceDeadline d
        (recurrencePhaseDefect Q) N :=
      (isUniversalPhaseCoherencePivotDeadline_iff hd).1 hN
    classical
    unfold universalPhaseCoherenceTime
    exact Nat.find_min' _ hdeadline
  exact ⟨hpivot, hminimal,
    universalPhaseCoherence_dimensionResolution_sandwich hd⟩

end

end RHTower
