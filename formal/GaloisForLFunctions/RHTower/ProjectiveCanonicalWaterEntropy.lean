import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherenceCeiling

/-!
# Canonical projective water entropy

The active water equation is solved when the requested distortion is below
the nonpivot mass.  Above that threshold the canonical level is one and the
entropy is zero.  This file joins both regimes, proves global optimality for
every pivot, and takes the finite projective minimum.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Existence of an active water level at or above one. -/
def HasProjectiveWaterLevel {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (η : ℝ) : Prop :=
  ∃ lam : ℝ, 1 ≤ lam ∧ projectiveWaterMass w k lam = η

/-- Canonical active/inactive water level. -/
noncomputable def projectiveCanonicalWaterLevel {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (η : ℝ) : ℝ := by
  classical
  exact if h : HasProjectiveWaterLevel w k η then Classical.choose h else 1

theorem projectiveCanonicalWaterLevel_spec_of_hasLevel
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (η : ℝ)
    (h : HasProjectiveWaterLevel w k η) :
    1 ≤ projectiveCanonicalWaterLevel w k η ∧
      projectiveWaterMass w k
        (projectiveCanonicalWaterLevel w k η) = η := by
  rw [projectiveCanonicalWaterLevel, dif_pos h]
  exact Classical.choose_spec h

theorem projectiveCanonicalWaterLevel_eq_one_of_not_hasLevel
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (η : ℝ)
    (h : ¬ HasProjectiveWaterLevel w k η) :
    projectiveCanonicalWaterLevel w k η = 1 := by
  rw [projectiveCanonicalWaterLevel, dif_neg h]

theorem projectiveCanonicalWaterLevel_pos
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (η : ℝ) :
    0 < projectiveCanonicalWaterLevel w k η := by
  by_cases h : HasProjectiveWaterLevel w k η
  · exact zero_lt_one.trans_le
      (projectiveCanonicalWaterLevel_spec_of_hasLevel w k η h).1
  · rw [projectiveCanonicalWaterLevel_eq_one_of_not_hasLevel w k η h]
    norm_num

theorem probabilityWeight_le_one
    {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) (k : Fin d) :
    w k ≤ 1 := by
  have hsingle : w k ≤ ∑ i, w i :=
    Finset.single_le_sum (fun i _hi ↦ hw i) (Finset.mem_univ k)
  simpa only [hmass] using hsingle

theorem projectiveWaterEntropyAt_one_eq_zero
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    projectiveWaterEntropyAt w k 1 = 0 := by
  rw [projectiveWaterEntropyAt]
  have hterm : ∀ i,
      (if i = k then 0 else Real.log (max 1 (1 * w i))) = 0 := by
    intro i
    by_cases hik : i = k
    · simp [hik]
    · simp only [hik, ↓reduceIte, one_mul]
      rw [max_eq_left (probabilityWeight_le_one w hw hmass i), Real.log_one]
  simp_rw [hterm]
  simp

theorem projectiveCoordinateEntropy_nonneg
    {d : ℕ} (k : Fin d) (x : Fin d → ℝ)
    (hx : ∀ i, 1 ≤ x i) :
    0 ≤ projectiveCoordinateEntropy k x := by
  rw [projectiveCoordinateEntropy]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _hi
  by_cases hik : i = k
  · simp [hik]
  · simp only [hik, ↓reduceIte]
    exact Real.log_nonneg (hx i)

/-- The canonical level satisfies the universal active-coordinate budget in
both the active and inactive regimes. -/
theorem projectiveCanonicalWaterLevel_mul_eta_le_card_sub_one
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ) (k : Fin d)
    {η : ℝ} (hη1 : η ≤ 1) :
    projectiveCanonicalWaterLevel w k η * η ≤ (d - 1 : ℕ) := by
  by_cases h : HasProjectiveWaterLevel w k η
  · obtain ⟨hlam, hlevel⟩ :=
      projectiveCanonicalWaterLevel_spec_of_hasLevel w k η h
    exact waterLevel_mul_eta_le_card_sub_one w k
      (zero_lt_one.trans_le hlam) hlevel
  · rw [projectiveCanonicalWaterLevel_eq_one_of_not_hasLevel w k η h,
      one_mul]
    have hcast : (1 : ℝ) ≤ (d - 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ d - 1)
    exact hη1.trans hcast

/-- The canonical water scale is feasible.  In the inactive regime this is
the all-one scale and its reciprocal mass is the full nonpivot mass. -/
theorem projectiveCanonicalWaterScale_feasible
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η : ℝ} (hη0 : 0 < η) :
    ProjectiveWaterFeasible w k η
      (projectiveWaterScale w k
        (projectiveCanonicalWaterLevel w k η)) := by
  by_cases h : HasProjectiveWaterLevel w k η
  · obtain ⟨hlam, hlevel⟩ :=
      projectiveCanonicalWaterLevel_spec_of_hasLevel w k η h
    exact projectiveWaterScale_feasible w k hw
      (zero_lt_one.trans_le hlam) hlevel
  · have htail : 1 - w k ≤ η := by
      by_contra hnot
      have hstrict : η < 1 - w k := lt_of_not_ge hnot
      obtain ⟨lam, hlam1, _hlamUpper, hlevel⟩ :=
        exists_projectiveWaterLevel hd w k hw hmass hη0 hstrict
      exact h ⟨lam, hlam1, hlevel⟩
    rw [projectiveCanonicalWaterLevel_eq_one_of_not_hasLevel w k η h]
    constructor
    · exact projectiveWaterScale_ge_one w k 1
    · rw [projectiveWaterScale_reciprocalMass w k 1 hw (by norm_num),
        projectiveWaterMass_one w k hw hmass]
      exact htail

/-- The canonical active/inactive scale globally minimizes coordinate
entropy on its pivot fibre. -/
theorem projectiveCanonicalWaterEntropy_le_of_feasible
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η : ℝ} (x : Fin d → ℝ) (hx : ProjectiveWaterFeasible w k η x) :
    projectiveWaterEntropyAt w k
        (projectiveCanonicalWaterLevel w k η) ≤
      projectiveCoordinateEntropy k x := by
  by_cases h : HasProjectiveWaterLevel w k η
  · obtain ⟨hlam, hlevel⟩ :=
      projectiveCanonicalWaterLevel_spec_of_hasLevel w k η h
    exact projectiveWaterEntropyAt_le_of_feasible w k hw
      (zero_lt_one.trans_le hlam) hlevel x hx
  · rw [projectiveCanonicalWaterLevel_eq_one_of_not_hasLevel w k η h,
      projectiveWaterEntropyAt_one_eq_zero w k hw hmass]
    exact projectiveCoordinateEntropy_nonneg k x hx.1

/-- Canonical pivot entropy. -/
def projectiveCanonicalWaterEntropy {d : ℕ}
    (w : Fin d → ℝ) (η : ℝ) (k : Fin d) : ℝ :=
  projectiveWaterEntropyAt w k (projectiveCanonicalWaterLevel w k η)

private theorem projectiveCanonicalWaterEntropy_values_nonempty
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (η : ℝ) :
    (Finset.univ.image (projectiveCanonicalWaterEntropy w η)).Nonempty := by
  classical
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let k : Fin d := Classical.choice (inferInstance : Nonempty (Fin d))
  exact ⟨projectiveCanonicalWaterEntropy w η k,
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩

/-- Minimum canonical entropy over all projective pivots. -/
noncomputable def projectiveCanonicalWaterEntropyMinimum
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (η : ℝ) : ℝ :=
  (Finset.univ.image (projectiveCanonicalWaterEntropy w η)).min'
    (projectiveCanonicalWaterEntropy_values_nonempty hd w η)

theorem projectiveCanonicalWaterEntropyMinimum_le
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (η : ℝ) (k : Fin d) :
    projectiveCanonicalWaterEntropyMinimum hd w η ≤
      projectiveCanonicalWaterEntropy w η k := by
  unfold projectiveCanonicalWaterEntropyMinimum
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)

theorem exists_projectiveCanonicalWaterEntropy_minimizingPivot
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (η : ℝ) :
    ∃ k : Fin d,
      projectiveCanonicalWaterEntropy w η k =
        projectiveCanonicalWaterEntropyMinimum hd w η := by
  have hmem := Finset.min'_mem
    (Finset.univ.image (projectiveCanonicalWaterEntropy w η))
    (projectiveCanonicalWaterEntropy_values_nonempty hd w η)
  rw [Finset.mem_image] at hmem
  obtain ⟨k, _hk, hk⟩ := hmem
  exact ⟨k, hk⟩

/-- **Universal projective water-entropy sandwich.**  For every finite
probability packet of dimension at least two and every nontrivial coherence
defect, one universal deadline is trapped between the same intrinsic minimum
water entropy, with explicit linear-in-dimension implementation costs. -/
theorem exists_universalProjectiveWeightedCoherenceDeadline_entropySandwich
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ T : ℕ,
      IsUniversalProjectiveWeightedCoherenceDeadline w η T ∧
      projectiveCanonicalWaterEntropyMinimum (by omega) w η -
          (Real.pi / 4) * (d - 1 : ℕ) - Real.log (2 * (d : ℝ)) <
        Real.log (T : ℝ) ∧
      Real.log (T : ℝ) ≤
        projectiveCanonicalWaterEntropyMinimum (by omega) w η +
          (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
  let hd0 : 0 < d := by omega
  let lam : Fin d → ℝ := fun k ↦ projectiveCanonicalWaterLevel w k η
  let H : ℝ := projectiveCanonicalWaterEntropyMinimum hd0 w η
  obtain ⟨k, hk⟩ :=
    exists_projectiveCanonicalWaterEntropy_minimizingPivot hd0 w η
  let x : Fin d → ℝ := projectiveWaterScale w k (lam k)
  have hx : ProjectiveWaterFeasible w k η x := by
    exact projectiveCanonicalWaterScale_feasible hd0 w k hw hmass hη0
  obtain ⟨T, hdeadline, hupper⟩ :=
    exists_universalProjectiveWeightedCoherenceDeadline_of_feasible
      w k x hw hmass hx
  refine ⟨T, hdeadline, ?_, ?_⟩
  · have hlower := projectiveWaterEntropy_sub_cost_lt_log_deadline
      hd0 w hw hmass hη0.le hη1 lam
      (fun j ↦ projectiveCanonicalWaterLevel_pos w j η)
      (fun j ↦ projectiveCanonicalWaterLevel_mul_eta_le_card_sub_one
        hd w j hη1)
      (fun j ↦ projectiveCanonicalWaterEntropyMinimum_le hd0 w η j)
      hdeadline
    simpa only [H, hd0, lam, projectiveCanonicalWaterEntropy] using hlower
  · calc
      Real.log (T : ℝ) ≤ projectiveCoordinateEntropy k x +
          (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := hupper
      _ = projectiveCanonicalWaterEntropy w η k +
          (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
        rw [projectiveCoordinateEntropy_waterScale]
        rfl
      _ = projectiveCanonicalWaterEntropyMinimum hd0 w η +
          (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
        rw [hk]

end RHTower
