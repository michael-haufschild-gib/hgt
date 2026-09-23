import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherenceAvoidance
import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherenceRecurrence

/-!
# Constructive weighted projective coherence ceiling

An arbitrary feasible coordinate-resolution profile yields a universal
weighted coherence deadline.  The logarithmic clock cost is the exact
coordinate entropy plus one universal constant per nonpivot coordinate.
-/

open Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Integer angular resolution attached to a real coordinate scale.  The
projective pivot costs one box. -/
def projectivePhaseResolution {d : ℕ}
    (k : Fin d) (x : Fin d → ℝ) (i : Fin d) : ℕ :=
  if i = k then 1 else Nat.ceil (Real.pi * Real.sqrt (2 * x i))

/-- Universal multiplicative rounding constant for one active coordinate. -/
def projectivePhaseResolutionConstant : ℝ :=
  2 * Real.pi * Real.sqrt 2

theorem projectivePhaseResolutionConstant_pos :
    0 < projectivePhaseResolutionConstant := by
  rw [projectivePhaseResolutionConstant]
  positivity

theorem projectivePhaseResolution_pos
    {d : ℕ} (k : Fin d) (x : Fin d → ℝ)
    (hx : ∀ i, 1 ≤ x i) (i : Fin d) :
    0 < projectivePhaseResolution k x i := by
  by_cases hik : i = k
  · simp [projectivePhaseResolution, hik]
  · rw [projectivePhaseResolution, if_neg hik]
    apply Nat.ceil_pos.mpr
    have hxi : 0 < x i := lt_of_lt_of_le zero_lt_one (hx i)
    positivity

theorem projectivePhaseResolution_cast_lower
    {d : ℕ} (k : Fin d) (x : Fin d → ℝ)
    (i : Fin d) (hik : i ≠ k) :
    Real.pi * Real.sqrt (2 * x i) ≤
      (projectivePhaseResolution k x i : ℝ) := by
  rw [projectivePhaseResolution, if_neg hik]
  exact Nat.le_ceil _

theorem projectivePhaseResolution_cast_upper
    {d : ℕ} (k : Fin d) (x : Fin d → ℝ)
    (hx : ∀ i, 1 ≤ x i) (i : Fin d) (hik : i ≠ k) :
    (projectivePhaseResolution k x i : ℝ) ≤
      projectivePhaseResolutionConstant * Real.sqrt (x i) := by
  let y : ℝ := Real.pi * Real.sqrt (2 * x i)
  have hxi : 0 < x i := lt_of_lt_of_le zero_lt_one (hx i)
  have hsqrtOne : 1 ≤ Real.sqrt (2 * x i) := by
    rw [Real.one_le_sqrt]
    nlinarith [hx i]
  have hpiOne : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hyOne : 1 ≤ y := by
    dsimp only [y]
    calc
      1 ≤ Real.pi := hpiOne
      _ ≤ Real.pi * Real.sqrt (2 * x i) := by
        simpa using mul_le_mul_of_nonneg_left hsqrtOne Real.pi_pos.le
  have hy0 : 0 ≤ y := hyOne.trans' zero_le_one
  have hceil : (Nat.ceil y : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have htwo : (Nat.ceil y : ℝ) ≤ 2 * y := by linarith
  rw [projectivePhaseResolution, if_neg hik]
  change (Nat.ceil y : ℝ) ≤ _
  calc
    (Nat.ceil y : ℝ) ≤ 2 * y := htwo
    _ = projectivePhaseResolutionConstant * Real.sqrt (x i) := by
      rw [projectivePhaseResolutionConstant]
      dsimp only [y]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- The quadratic phase loss supplied by the rounded resolution is at most
the reciprocal coordinate scale. -/
theorem projectivePhaseResolution_defect_le_reciprocal
    {d : ℕ} (k : Fin d) (x w : Fin d → ℝ)
    (hx : ∀ i, 1 ≤ x i) (hw : ∀ i, 0 ≤ w i) (i : Fin d) :
    (if i = k then 0 else
      w i * ((2 * Real.pi /
        (projectivePhaseResolution k x i : ℝ)) ^ (2 : ℕ) / 2)) ≤
      if i = k then 0 else w i / x i := by
  by_cases hik : i = k
  · simp [hik]
  · simp only [hik, ↓reduceIte]
    have hxi : 0 < x i := lt_of_lt_of_le zero_lt_one (hx i)
    have hQposNat := projectivePhaseResolution_pos k x hx i
    have hQpos : 0 < (projectivePhaseResolution k x i : ℝ) :=
      Nat.cast_pos.mpr hQposNat
    have hlower := projectivePhaseResolution_cast_lower k x i hik
    have hsquare :=
      (sq_le_sq₀
        (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg _)) hQpos.le).2 hlower
    have hsqrt : Real.sqrt (2 * x i) ^ (2 : ℕ) = 2 * x i :=
      Real.sq_sqrt (by positivity)
    have hden :
        2 * Real.pi ^ (2 : ℕ) * x i ≤
          (projectivePhaseResolution k x i : ℝ) ^ (2 : ℕ) := by
      rw [mul_pow, hsqrt] at hsquare
      nlinarith
    have hscalar :
        (2 * Real.pi /
          (projectivePhaseResolution k x i : ℝ)) ^ (2 : ℕ) / 2 ≤
        1 / x i := by
      calc
        (2 * Real.pi /
            (projectivePhaseResolution k x i : ℝ)) ^ (2 : ℕ) / 2 =
            (2 * Real.pi ^ (2 : ℕ)) /
              (projectivePhaseResolution k x i : ℝ) ^ (2 : ℕ) := by
          field_simp [hQpos.ne']
        _ ≤ 1 / x i := by
          apply (div_le_div_iff₀ (sq_pos_of_pos hQpos) hxi).2
          simpa only [one_mul] using hden
    have hmul := mul_le_mul_of_nonneg_left hscalar (hw i)
    simpa only [div_eq_mul_inv, one_mul] using hmul

theorem sum_projectivePhaseResolution_defect_le_reciprocal
    {d : ℕ} (k : Fin d) (x w : Fin d → ℝ)
    (hx : ∀ i, 1 ≤ x i) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, if i = k then 0 else
      w i * ((2 * Real.pi /
        (projectivePhaseResolution k x i : ℝ)) ^ (2 : ℕ) / 2)) ≤
      ∑ i, if i = k then 0 else w i / x i := by
  exact Finset.sum_le_sum fun i _hi ↦
    projectivePhaseResolution_defect_le_reciprocal k x w hx hw i

/-- Every feasible projective coordinate profile supplies a universal
deadline at the product of its rounded resolutions. -/
theorem isUniversalProjectiveWeightedCoherenceDeadline_of_feasible
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {η : ℝ}
    (x : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1)
    (hx : ProjectiveWaterFeasible w k η x) :
    IsUniversalProjectiveWeightedCoherenceDeadline w η
      (∏ i, projectivePhaseResolution k x i) := by
  intro ω
  obtain ⟨n, hn0, hnQ, hncoh⟩ :=
    exists_projective_nonnegative_weighted_phaseSum_recurrence_anisotropic
      ω w (projectivePhaseResolution k x) k
        (projectivePhaseResolution_pos k x hx.1) hw hmass
  refine ⟨n, hn0, hnQ, ?_⟩
  have hdefect :=
    (sum_projectivePhaseResolution_defect_le_reciprocal
      k x w hx.1 hw).trans hx.2
  exact (sub_le_sub_left hdefect 1).trans hncoh

/-- The rounded product clock pays the exact coordinate entropy and at most
one universal logarithmic constant for each nonpivot coordinate. -/
theorem log_prod_projectivePhaseResolution_le
    {d : ℕ} (k : Fin d) (x : Fin d → ℝ)
    (hx : ∀ i, 1 ≤ x i) :
    Real.log ((∏ i, projectivePhaseResolution k x i : ℕ) : ℝ) ≤
      projectiveCoordinateEntropy k x +
        (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
  have hQpos : ∀ i, 0 < projectivePhaseResolution k x i :=
    projectivePhaseResolution_pos k x hx
  have hterm : ∀ i : Fin d,
      Real.log (projectivePhaseResolution k x i : ℝ) ≤
        if i = k then 0 else
          (1 / 2 : ℝ) * Real.log (x i) +
            Real.log projectivePhaseResolutionConstant := by
    intro i
    by_cases hik : i = k
    · simp [projectivePhaseResolution, hik]
    · simp only [hik, ↓reduceIte]
      have hxi : 0 < x i := lt_of_lt_of_le zero_lt_one (hx i)
      have hQi : 0 < (projectivePhaseResolution k x i : ℝ) :=
        Nat.cast_pos.mpr (hQpos i)
      have hright :
          0 < projectivePhaseResolutionConstant * Real.sqrt (x i) := by
        exact mul_pos projectivePhaseResolutionConstant_pos
          (Real.sqrt_pos.mpr hxi)
      have hlog := Real.strictMonoOn_log.monotoneOn
        (show (projectivePhaseResolution k x i : ℝ) ∈ Set.Ioi 0 from hQi)
        (show projectivePhaseResolutionConstant * Real.sqrt (x i) ∈
          Set.Ioi 0 from hright)
        (projectivePhaseResolution_cast_upper k x hx i hik)
      rw [Real.log_mul projectivePhaseResolutionConstant_pos.ne'
          (Real.sqrt_pos.mpr hxi).ne',
        Real.log_sqrt hxi.le] at hlog
      nlinarith
  have hcastProd :
      (((∏ i, projectivePhaseResolution k x i : ℕ) : ℕ) : ℝ) =
        ∏ i, (projectivePhaseResolution k x i : ℝ) := by
    norm_num
  rw [hcastProd, Real.log_prod (fun i _hi ↦
    (Nat.cast_ne_zero.mpr (hQpos i).ne'))]
  calc
    (∑ i, Real.log (projectivePhaseResolution k x i : ℝ)) ≤
        ∑ i, if i = k then 0 else
          (1 / 2 : ℝ) * Real.log (x i) +
            Real.log projectivePhaseResolutionConstant :=
      Finset.sum_le_sum fun i _hi ↦ hterm i
    _ = projectiveCoordinateEntropy k x +
        (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
      rw [projectiveCoordinateEntropy]
      have hsplit :
          (∑ i, if i = k then 0 else
            (1 / 2 : ℝ) * Real.log (x i) +
              Real.log projectivePhaseResolutionConstant) =
            (∑ i, (1 / 2 : ℝ) *
              (if i = k then 0 else Real.log (x i))) +
            ∑ i, (if i = k then 0 else
              Real.log projectivePhaseResolutionConstant) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hik : i = k <;> simp [hik]
      rw [hsplit, ← Finset.mul_sum]
      congr 1
      have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun hd0 ↦ by
        subst d
        exact Fin.elim0 k
      calc
        (∑ i, if i = k then 0 else
            Real.log projectivePhaseResolutionConstant) =
            ∑ i, (Real.log projectivePhaseResolutionConstant -
              if i = k then Real.log projectivePhaseResolutionConstant
              else 0) := by
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hik : i = k <;> simp [hik]
        _ = (d : ℝ) * Real.log projectivePhaseResolutionConstant -
            Real.log projectivePhaseResolutionConstant := by
          rw [Finset.sum_sub_distrib]
          simp
        _ = (d - 1 : ℕ) *
            Real.log projectivePhaseResolutionConstant := by
          rw [Nat.cast_sub hd]
          push_cast
          ring

/-- A feasible profile yields a universal deadline whose logarithm is
bounded by its projective coordinate entropy plus the rounding cost. -/
theorem exists_universalProjectiveWeightedCoherenceDeadline_of_feasible
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {η : ℝ}
    (x : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1)
    (hx : ProjectiveWaterFeasible w k η x) :
    ∃ T : ℕ,
      IsUniversalProjectiveWeightedCoherenceDeadline w η T ∧
      Real.log (T : ℝ) ≤ projectiveCoordinateEntropy k x +
        (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
  refine ⟨∏ i, projectivePhaseResolution k x i,
    isUniversalProjectiveWeightedCoherenceDeadline_of_feasible
      w k x hw hmass hx, ?_⟩
  exact log_prod_projectivePhaseResolution_le k x hx.1

/-- Exact water filling therefore supplies the constructive entropy ceiling. -/
theorem exists_universalProjectiveWeightedCoherenceDeadline_waterScale
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {η lam : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hlam : 0 < lam) (hlevel : projectiveWaterMass w k lam = η) :
    ∃ T : ℕ,
      IsUniversalProjectiveWeightedCoherenceDeadline w η T ∧
      Real.log (T : ℝ) ≤ projectiveWaterEntropyAt w k lam +
        (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
  obtain ⟨T, hdeadline, hlog⟩ :=
    exists_universalProjectiveWeightedCoherenceDeadline_of_feasible
      w k (projectiveWaterScale w k lam) hw hmass
        (projectiveWaterScale_feasible w k hw hlam hlevel)
  refine ⟨T, hdeadline, ?_⟩
  rwa [projectiveCoordinateEntropy_waterScale] at hlog

end RHTower
