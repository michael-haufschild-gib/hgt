import GaloisForLFunctions.HTGeometry.UniversalProjectiveRecurrenceCapstoneLaw
import GaloisForLFunctions.HTGeometry.ArithmeticTemporalRankInstability

/-!
# Dense stratification of projective recurrence

Every positive projective temporal dimension occurs densely in finite
spectral space.  From three levels onward, completed recurrence dimension is
therefore nowhere continuous.  Rank conservation transfers this result to
the dual relation rank: maximally free and strongly constrained recurrence
phases both occur arbitrarily near every spectrum.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reconstruct an energy packet from one anchor and its projective gaps. -/
def energyWithProjectiveGaps {d : ℕ}
    (anchor : ℝ) (gap : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases anchor (fun i => anchor + gap i)

@[simp] theorem projectiveGapPacket_energyWithProjectiveGaps
    {d : ℕ} (anchor : ℝ) (gap : Fin d → ℝ) :
    projectiveGapPacket (energyWithProjectiveGaps anchor gap) = gap := by
  funext i
  simp [projectiveGapPacket, energyWithProjectiveGaps]

theorem exists_exactProjectiveTemporalRank_close
    {d k : ℕ} (hk : 0 < k) (hkd : k ≤ d)
    (energy : Fin (d + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ perturbed : Fin (d + 1) → ℝ,
      projectiveTemporalRank perturbed = k ∧
      ∀ i, dist (perturbed i) (energy i) < ε := by
  obtain ⟨gap, hgaprank, hgapclose⟩ :=
    (dense_exactRationalRank hk hkd).exists_dist_lt
      (projectiveGapPacket energy) hε
  rw [dist_pi_lt_iff hε] at hgapclose
  let perturbed := energyWithProjectiveGaps (energy 0) gap
  refine ⟨perturbed, ?_, ?_⟩
  · rw [projectiveTemporalRank, projectiveGapPacket_energyWithProjectiveGaps]
    exact hgaprank
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [perturbed, energyWithProjectiveGaps] using hε
    · simpa [perturbed, energyWithProjectiveGaps, projectiveGapPacket,
        dist_add_left, dist_comm, add_comm] using hgapclose j

/-- Every positive admissible projective time dimension is dense. -/
theorem dense_exactProjectiveTemporalRank
    {d k : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    Dense {energy : Fin (d + 1) → ℝ |
      projectiveTemporalRank energy = k} := by
  rw [Metric.dense_iff]
  intro energy ε hε
  obtain ⟨perturbed, hrank, hclose⟩ :=
    exists_exactProjectiveTemporalRank_close hk hkd energy ε hε
  refine ⟨perturbed, ?_, hrank⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  exact hclose

/-- From three levels onward, projective temporal rank is nowhere continuous. -/
theorem projectiveTemporalRank_nowhereContinuous
    {d : ℕ} (hd : 2 ≤ d) (energy : Fin (d + 1) → ℝ) :
    ¬ ContinuousAt projectiveTemporalRank energy := by
  intro hcont
  let k : ℕ := if projectiveTemporalRank energy = 1 then 2 else 1
  have hkpos : 0 < k := by
    dsimp [k]
    split <;> omega
  have hkle : k ≤ d := by
    dsimp [k]
    split <;> omega
  have hkne : k ≠ projectiveTemporalRank energy := by
    dsimp [k]
    split <;> omega
  have hev :
      {y : Fin (d + 1) → ℝ |
        projectiveTemporalRank y = projectiveTemporalRank energy} ∈
        𝓝 energy := by
    have hnat :
        ∀ᶠ z : ℕ in 𝓝 (projectiveTemporalRank energy),
          z = projectiveTemporalRank energy := by
      simp
    exact hcont.eventually hnat
  obtain ⟨y, hyrank, hyeq⟩ :=
    (dense_exactProjectiveTemporalRank hkpos hkle).inter_nhds_nonempty hev
  exact hkne (hyrank.symm.trans hyeq)

/-- Every positive dimension of the completed recurrence ensemble is dense. -/
theorem dense_exactCompletedRecurrenceTemporalDimension
    {d k : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    Dense {energy : Fin (d + 1) → ℝ |
      phaseLawTemporalDimension (spectralRelationPhaseEnsemble energy) = k} := by
  simpa only [relationPhaseEnsemble_temporalDimension_eq_projectiveRank] using
    (dense_exactProjectiveTemporalRank hk hkd)

/-- Completed recurrence temporal dimension is nowhere continuous from three levels onward. -/
theorem completedRecurrenceTemporalDimension_nowhereContinuous
    {d : ℕ} (hd : 2 ≤ d) (energy : Fin (d + 1) → ℝ) :
    ¬ ContinuousAt
      (fun e : Fin (d + 1) → ℝ =>
        phaseLawTemporalDimension (spectralRelationPhaseEnsemble e)) energy := by
  simpa only [relationPhaseEnsemble_temporalDimension_eq_projectiveRank] using
    (projectiveTemporalRank_nowhereContinuous hd energy)

/-- Every relation rank dual to a positive temporal rank is dense. -/
theorem dense_exactProjectiveRelationRank
    {d k : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    Dense {energy : Fin (d + 1) → ℝ |
      Module.finrank ℚ (projectiveSpectralRelationRationalSpace energy) = d - k} := by
  apply (dense_exactProjectiveTemporalRank hk hkd).mono
  intro energy henergy
  have hconservation := projectiveTemporalRank_add_relationRank energy
  rw [henergy] at hconservation
  exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hconservation)

/-- With at least three levels, free and positive-rank constrained phases are both dense. -/
theorem dense_free_and_constrained_completedRecurrencePhases
    {d : ℕ} (hd : 2 ≤ d) :
    Dense {energy : Fin (d + 1) → ℝ |
      Module.finrank ℚ (projectiveSpectralRelationRationalSpace energy) = 0} ∧
    Dense {energy : Fin (d + 1) → ℝ |
      Module.finrank ℚ (projectiveSpectralRelationRationalSpace energy) = d - 1} := by
  constructor
  · simpa using dense_exactProjectiveRelationRank (k := d) (by omega) le_rfl
  · exact dense_exactProjectiveRelationRank (k := 1) (by omega) (by omega)

end
end GaloisForLFunctions.HTGeometry
