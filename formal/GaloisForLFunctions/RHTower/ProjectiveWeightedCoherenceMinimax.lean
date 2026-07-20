import GaloisForLFunctions.RHTower.ProjectiveWaterEntropyConsequences

/-!
# Exact weighted projective minimax time

The least universal deadline exists by the constructive water-entropy
ceiling.  Since the Haar argument bounds every universal deadline from below,
the least deadline itself obeys the two-sided canonical entropy law.
-/

noncomputable section

namespace RHTower

theorem exists_universalProjectiveWeightedCoherenceDeadline
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ T : ℕ, IsUniversalProjectiveWeightedCoherenceDeadline w η T := by
  obtain ⟨T, hdeadline, _hlower, _hupper⟩ :=
    exists_universalProjectiveWeightedCoherenceDeadline_entropySandwich
      hd w hw hmass hη0 hη1
  exact ⟨T, hdeadline⟩

/-- Least positive-clock deadline which works for every frequency packet. -/
noncomputable def universalProjectiveWeightedCoherenceTime
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) : ℕ := by
  classical
  exact Nat.find (exists_universalProjectiveWeightedCoherenceDeadline
    hd w hw hmass η hη0 hη1)

theorem universalProjectiveWeightedCoherenceTime_isDeadline
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    IsUniversalProjectiveWeightedCoherenceDeadline w η
      (universalProjectiveWeightedCoherenceTime
        hd w hw hmass η hη0 hη1) := by
  classical
  unfold universalProjectiveWeightedCoherenceTime
  exact Nat.find_spec _

theorem universalProjectiveWeightedCoherenceTime_le_of_deadline
    {d T : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hdeadline : IsUniversalProjectiveWeightedCoherenceDeadline w η T) :
    universalProjectiveWeightedCoherenceTime
      hd w hw hmass η hη0 hη1 ≤ T := by
  classical
  unfold universalProjectiveWeightedCoherenceTime
  exact Nat.find_min' _ hdeadline

theorem universalProjectiveWeightedCoherenceTime_pos
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    0 < universalProjectiveWeightedCoherenceTime
      hd w hw hmass η hη0 hη1 := by
  obtain ⟨n, hn0, hnT, _hncoh⟩ :=
    universalProjectiveWeightedCoherenceTime_isDeadline
      hd w hw hmass η hη0 hη1 (fun _ ↦ 0)
  exact hn0.trans_le hnT

/-- **Exact minimax projective water-entropy sandwich.** -/
theorem universalProjectiveWeightedCoherenceTime_entropySandwich
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    projectiveCanonicalWaterEntropyMinimum (by omega) w η -
        (Real.pi / 4) * (d - 1 : ℕ) - Real.log (2 * (d : ℝ)) <
      Real.log (universalProjectiveWeightedCoherenceTime
        hd w hw hmass η hη0 hη1 : ℝ) ∧
    Real.log (universalProjectiveWeightedCoherenceTime
        hd w hw hmass η hη0 hη1 : ℝ) ≤
      projectiveCanonicalWaterEntropyMinimum (by omega) w η +
        (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
  let hd0 : 0 < d := by omega
  let lam : Fin d → ℝ := fun k ↦ projectiveCanonicalWaterLevel w k η
  let Tmin : ℕ := universalProjectiveWeightedCoherenceTime
    hd w hw hmass η hη0 hη1
  have hminDeadline : IsUniversalProjectiveWeightedCoherenceDeadline w η Tmin := by
    exact universalProjectiveWeightedCoherenceTime_isDeadline
      hd w hw hmass η hη0 hη1
  have hlower := projectiveWaterEntropy_sub_cost_lt_log_deadline
    hd0 w hw hmass hη0.le hη1 lam
    (fun k ↦ projectiveCanonicalWaterLevel_pos w k η)
    (fun k ↦ projectiveCanonicalWaterLevel_mul_eta_le_card_sub_one
      hd w k hη1)
    (fun k ↦ projectiveCanonicalWaterEntropyMinimum_le hd0 w η k)
    hminDeadline
  obtain ⟨T, hdeadline, _hlowerT, hupperT⟩ :=
    exists_universalProjectiveWeightedCoherenceDeadline_entropySandwich
      hd w hw hmass hη0 hη1
  have hminle : Tmin ≤ T :=
    universalProjectiveWeightedCoherenceTime_le_of_deadline
      hd w hw hmass η hη0 hη1 hdeadline
  have hTminPos : 0 < (Tmin : ℝ) := by
    exact_mod_cast universalProjectiveWeightedCoherenceTime_pos
      hd w hw hmass η hη0 hη1
  have hTpos : 0 < (T : ℝ) := by
    have : 0 < T := (universalProjectiveWeightedCoherenceTime_pos
      hd w hw hmass η hη0 hη1).trans_le hminle
    exact_mod_cast this
  have hlogle : Real.log (Tmin : ℝ) ≤ Real.log (T : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hTminPos hTpos (by exact_mod_cast hminle)
  constructor
  · simpa only [Tmin, lam, hd0, projectiveCanonicalWaterEntropy] using hlower
  · exact hlogle.trans hupperT

/-- Relative form of the exact minimax law. -/
theorem universalProjectiveWeightedCoherenceTime_normalized
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η ε : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hH : 0 < projectiveCanonicalWaterEntropyMinimum (by omega) w η)
    (hlower : projectiveWaterLowerCarrierCost d ≤
      ε * projectiveCanonicalWaterEntropyMinimum (by omega) w η)
    (hupper : projectiveWaterUpperCarrierCost d ≤
      ε * projectiveCanonicalWaterEntropyMinimum (by omega) w η) :
    1 - ε <
        Real.log (universalProjectiveWeightedCoherenceTime
          hd w hw hmass η hη0 hη1 : ℝ) /
          projectiveCanonicalWaterEntropyMinimum (by omega) w η ∧
      Real.log (universalProjectiveWeightedCoherenceTime
          hd w hw hmass η hη0 hη1 : ℝ) /
          projectiveCanonicalWaterEntropyMinimum (by omega) w η ≤ 1 + ε := by
  let hd0 : 0 < d := by omega
  let H : ℝ := projectiveCanonicalWaterEntropyMinimum hd0 w η
  let Tmin : ℕ := universalProjectiveWeightedCoherenceTime
    hd w hw hmass η hη0 hη1
  obtain ⟨hlowerT, hupperT⟩ :=
    universalProjectiveWeightedCoherenceTime_entropySandwich
      hd w hw hmass η hη0 hη1
  have hH' : 0 < H := by simpa only [H, hd0] using hH
  have hlowCost : projectiveWaterLowerCarrierCost d ≤ ε * H := by
    simpa only [H, hd0] using hlower
  have huppCost : projectiveWaterUpperCarrierCost d ≤ ε * H := by
    simpa only [H, hd0] using hupper
  have hlowerExpanded : H - projectiveWaterLowerCarrierCost d <
      Real.log (Tmin : ℝ) := by
    have hraw : H - (Real.pi / 4) * (d - 1 : ℕ) -
        Real.log (2 * (d : ℝ)) < Real.log (Tmin : ℝ) := by
      simpa only [H, hd0, Tmin] using hlowerT
    rw [projectiveWaterLowerCarrierCost]
    linarith
  have hupperExpanded : Real.log (Tmin : ℝ) ≤
      H + projectiveWaterUpperCarrierCost d := by
    simpa only [H, hd0, Tmin, projectiveWaterUpperCarrierCost] using hupperT
  constructor
  · apply (lt_div_iff₀ hH').2
    have : H * (1 - ε) ≤ H - projectiveWaterLowerCarrierCost d := by
      nlinarith
    simpa only [mul_comm] using this.trans_lt hlowerExpanded
  · apply (div_le_iff₀ hH').2
    have : H + projectiveWaterUpperCarrierCost d ≤ H * (1 + ε) := by
      nlinarith
    simpa only [mul_comm] using hupperExpanded.trans this

end RHTower
