import GaloisForLFunctions.RHTower.ProjectiveCanonicalWaterEntropy

/-!
# Consequences of the projective water-entropy sandwich

The canonical entropy is supported exactly on coordinates above the water
line.  When this intrinsic entropy dominates the universal linear carrier
cost, the finite minimax clock has a constant-free relative law.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Nonpivot coordinates lying strictly above a proposed water line. -/
def projectiveWaterActiveCoordinates {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun j ↦ j ≠ k ∧ 1 < lam * w j

/-- **Exact active-coordinate entropy.**  Coordinates on or below the water
line contribute identically zero, not merely a small error. -/
theorem projectiveWaterEntropyAt_eq_sum_active
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) :
    projectiveWaterEntropyAt w k lam =
      (1 / 2 : ℝ) *
        ∑ j ∈ projectiveWaterActiveCoordinates w k lam,
          Real.log (lam * w j) := by
  rw [projectiveWaterEntropyAt, projectiveWaterActiveCoordinates]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hjk : j = k
  · simp [hjk]
  · by_cases hactive : 1 < lam * w j
    · simp [hjk, hactive, max_eq_right hactive.le]
    · have hinactive : lam * w j ≤ 1 := le_of_not_gt hactive
      simp [hjk, hactive, max_eq_left hinactive]

theorem projectiveWaterActiveCoordinates_not_mem_pivot
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) :
    k ∉ projectiveWaterActiveCoordinates w k lam := by
  simp [projectiveWaterActiveCoordinates]

theorem card_projectiveWaterActiveCoordinates_le_card_sub_one
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) :
    (projectiveWaterActiveCoordinates w k lam).card ≤ d - 1 := by
  have hsubset : projectiveWaterActiveCoordinates w k lam ⊆
      Finset.univ.erase k := by
    intro j hj
    rw [projectiveWaterActiveCoordinates, Finset.mem_filter] at hj
    simp [hj.2.1]
  calc
    (projectiveWaterActiveCoordinates w k lam).card ≤
        (Finset.univ.erase k).card := Finset.card_le_card hsubset
    _ = d - 1 := by simp

/-- Explicit extensive cost on the Haar-avoidance side. -/
def projectiveWaterLowerCarrierCost (d : ℕ) : ℝ :=
  (Real.pi / 4) * (d - 1 : ℕ) + Real.log (2 * (d : ℝ))

/-- Explicit extensive cost on the recurrence side. -/
def projectiveWaterUpperCarrierCost (d : ℕ) : ℝ :=
  (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant

/-- **Finite constant-free regime.**  Whenever the canonical entropy absorbs
both explicit carrier costs within relative tolerance `ε`, some universal
deadline has logarithmic cost within the same relative tolerance of the
canonical entropy.  This is the finite form of the superextensive law. -/
theorem exists_universalProjectiveWeightedCoherenceDeadline_normalized
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η ε : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hH : 0 < projectiveCanonicalWaterEntropyMinimum (by omega) w η)
    (hlower : projectiveWaterLowerCarrierCost d ≤
      ε * projectiveCanonicalWaterEntropyMinimum (by omega) w η)
    (hupper : projectiveWaterUpperCarrierCost d ≤
      ε * projectiveCanonicalWaterEntropyMinimum (by omega) w η) :
    ∃ T : ℕ,
      IsUniversalProjectiveWeightedCoherenceDeadline w η T ∧
      1 - ε < Real.log (T : ℝ) /
        projectiveCanonicalWaterEntropyMinimum (by omega) w η ∧
      Real.log (T : ℝ) /
        projectiveCanonicalWaterEntropyMinimum (by omega) w η ≤ 1 + ε := by
  let hd0 : 0 < d := by omega
  let H : ℝ := projectiveCanonicalWaterEntropyMinimum hd0 w η
  obtain ⟨T, hdeadline, hlowerT, hupperT⟩ :=
    exists_universalProjectiveWeightedCoherenceDeadline_entropySandwich
      hd w hw hmass hη0 hη1
  have hlowCost : projectiveWaterLowerCarrierCost d ≤ ε * H := by
    simpa only [H, hd0] using hlower
  have huppCost : projectiveWaterUpperCarrierCost d ≤ ε * H := by
    simpa only [H, hd0] using hupper
  have hH' : 0 < H := by simpa only [H, hd0] using hH
  have hlowerExpanded : H - projectiveWaterLowerCarrierCost d <
      Real.log (T : ℝ) := by
    have hraw : H - (Real.pi / 4) * (d - 1 : ℕ) -
        Real.log (2 * (d : ℝ)) < Real.log (T : ℝ) := by
      simpa only [H, hd0] using hlowerT
    rw [projectiveWaterLowerCarrierCost]
    linarith
  have hupperExpanded : Real.log (T : ℝ) ≤
      H + projectiveWaterUpperCarrierCost d := by
    simpa only [H, hd0, projectiveWaterUpperCarrierCost] using hupperT
  refine ⟨T, hdeadline, ?_, ?_⟩
  · apply (lt_div_iff₀ hH').2
    have : H * (1 - ε) ≤ H - projectiveWaterLowerCarrierCost d := by
      nlinarith
    simpa only [mul_comm] using this.trans_lt hlowerExpanded
  · apply (div_le_iff₀ hH').2
    have : H + projectiveWaterUpperCarrierCost d ≤ H * (1 + ε) := by
      nlinarith
    simpa only [mul_comm] using hupperExpanded.trans this

end RHTower
