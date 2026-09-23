import GaloisForLFunctions.HTGeometry.PhaseChordTailInterval

/-!
# Exact arithmetic certificate for failure of literal laboratory monotonicity
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

def monotonicityCounterLength : ℕ := 16384
noncomputable def monotonicityCounterEpsilon : ℝ := 1 / 1024
noncomputable def monotonicityCounterDelta : ℝ := 1 / 1000000
noncomputable def monotonicityCounterLateTime : ℝ := 2 * Real.pi
noncomputable def monotonicityCounterEarlyTime : ℝ :=
  2 * Real.pi - monotonicityCounterDelta
def monotonicityCounterMatchingCutoff : ℕ := 1477
def monotonicityCounterBridgeCutoff : ℕ := 38
def monotonicityCounterGateBudget : ℕ := 1513

noncomputable def monotonicityCounterTail : ℝ :=
  (∑ n ∈ Finset.Ioc monotonicityCounterMatchingCutoff monotonicityCounterLength,
      (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) +
    ∑ n ∈ Finset.Ioc monotonicityCounterBridgeCutoff monotonicityCounterLength,
      (1 : ℝ) / (n : ℝ) ^ (4 : ℕ)

theorem monotonicityCounterTail_nonneg : 0 ≤ monotonicityCounterTail := by
  unfold monotonicityCounterTail
  positivity

theorem monotonicityCounterTail_upper :
    monotonicityCounterTail ≤
      2 / 2955 - 2 / 32769 +
        (8 / 3 : ℝ) * (1 / 77 ^ (3 : ℕ) - 1 / 32769 ^ (3 : ℕ)) := by
  have hs := sum_inv_sq_Ioc_le_halfstep 1477 16384 (by omega) (by omega)
  have hb := sum_inv_fourth_Ioc_le_halfstep 38 16384 (by omega) (by omega)
  unfold monotonicityCounterTail monotonicityCounterMatchingCutoff
    monotonicityCounterBridgeCutoff monotonicityCounterLength
  calc
    (∑ n ∈ Finset.Ioc (1477 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) +
          ∑ n ∈ Finset.Ioc (38 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (4 : ℕ) ≤
        (2 / (2 * 1477 + 1 : ℕ) - 2 / (2 * 16384 + 1 : ℕ)) +
          (8 / 3 : ℝ) *
            (1 / ((2 * 38 + 1 : ℕ) : ℝ) ^ (3 : ℕ) -
              1 / ((2 * 16384 + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := add_le_add hs hb
    _ = 2 / 2955 - 2 / 32769 +
          (8 / 3 : ℝ) * (1 / 77 ^ (3 : ℕ) - 1 / 32769 ^ (3 : ℕ)) := by norm_num

theorem monotonicityCounterTail_lower :
    1 / 1478 - 1 / 16385 +
          (1 / 2 : ℝ) * (1 / 1478 ^ (2 : ℕ) - 1 / 16385 ^ (2 : ℕ)) +
        ((1 / 3 : ℝ) * (1 / 39 ^ (3 : ℕ) - 1 / 16385 ^ (3 : ℕ)) +
          (1 / 2 : ℝ) * (1 / 39 ^ (4 : ℕ) - 1 / 16385 ^ (4 : ℕ))) ≤
      monotonicityCounterTail := by
  have hs := sum_inv_sq_Ioc_ge_twoterm 1477 16384 (by omega)
  have hb := sum_inv_fourth_Ioc_ge_twoterm 38 16384 (by omega)
  unfold monotonicityCounterTail monotonicityCounterMatchingCutoff
    monotonicityCounterBridgeCutoff monotonicityCounterLength
  calc
    1 / 1478 - 1 / 16385 +
          (1 / 2 : ℝ) * (1 / 1478 ^ (2 : ℕ) - 1 / 16385 ^ (2 : ℕ)) +
        ((1 / 3 : ℝ) * (1 / 39 ^ (3 : ℕ) - 1 / 16385 ^ (3 : ℕ)) +
          (1 / 2 : ℝ) * (1 / 39 ^ (4 : ℕ) - 1 / 16385 ^ (4 : ℕ))) =
        (1 / (((1477 + 1 : ℕ) : ℝ)) - 1 / (((16384 + 1 : ℕ) : ℝ)) +
            (1 / 2 : ℝ) *
              (1 / (((1477 + 1 : ℕ) : ℝ)) ^ (2 : ℕ) -
                1 / (((16384 + 1 : ℕ) : ℝ)) ^ (2 : ℕ))) +
          ((1 / 3 : ℝ) *
              (1 / (((38 + 1 : ℕ) : ℝ)) ^ (3 : ℕ) -
                1 / (((16384 + 1 : ℕ) : ℝ)) ^ (3 : ℕ)) +
            (1 / 2 : ℝ) *
              (1 / (((38 + 1 : ℕ) : ℝ)) ^ (4 : ℕ) -
                1 / (((16384 + 1 : ℕ) : ℝ)) ^ (4 : ℕ))) := by norm_num
    _ ≤ (∑ n ∈ Finset.Ioc (1477 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) +
          ∑ n ∈ Finset.Ioc (38 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (4 : ℕ) := add_le_add hs hb

/-- At the exact `2π` time, omitted folded phase mass is strictly below `4ε`. -/
theorem monotonicityCounterLateTail_lt_fourEpsilon :
    monotonicityCounterLateTime * monotonicityCounterTail <
      4 * monotonicityCounterEpsilon := by
  have hW := monotonicityCounterTail_upper
  have hpi := Real.pi_lt_d6
  have hW0 := monotonicityCounterTail_nonneg
  have hpi' : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    norm_num at hpi ⊢
    exact hpi.le
  unfold monotonicityCounterLateTime monotonicityCounterEpsilon
  calc
    2 * Real.pi * monotonicityCounterTail ≤
        2 * (3141593 / 1000000 : ℝ) *
          (2 / 2955 - 2 / 32769 +
            (8 / 3 : ℝ) * (1 / 77 ^ (3 : ℕ) - 1 / 32769 ^ (3 : ℕ))) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpi' (by norm_num)) hW
        monotonicityCounterTail_nonneg
        (mul_nonneg (by positivity) (by norm_num))
    _ < 4 * (1 / 1024 : ℝ) := by norm_num

noncomputable def monotonicityCounterTailFloor : ℝ :=
  1 / 1478 - 1 / 16385 +
      (1 / 2 : ℝ) * (1 / 1478 ^ (2 : ℕ) - 1 / 16385 ^ (2 : ℕ)) +
    ((1 / 3 : ℝ) * (1 / 39 ^ (3 : ℕ) - 1 / 16385 ^ (3 : ℕ)) +
      (1 / 2 : ℝ) * (1 / 39 ^ (4 : ℕ) - 1 / 16385 ^ (4 : ℕ)))

noncomputable def monotonicityCounterTailPhaseFloor : ℝ :=
  monotonicityCounterDelta +
    (2 * (3141592 / 1000000 : ℝ) - monotonicityCounterDelta) *
      monotonicityCounterTailFloor

theorem monotonicityCounterTailPhaseFloor_pos : 0 < monotonicityCounterTailPhaseFloor := by
  unfold monotonicityCounterTailPhaseFloor monotonicityCounterTailFloor monotonicityCounterDelta
  norm_num

theorem monotonicityCounterTailPhaseFloor_sub_cube_gt :
    4 * monotonicityCounterEpsilon <
      monotonicityCounterTailPhaseFloor - monotonicityCounterTailPhaseFloor ^ (3 : ℕ) / 24 := by
  unfold monotonicityCounterTailPhaseFloor monotonicityCounterTailFloor
    monotonicityCounterDelta monotonicityCounterEpsilon
  norm_num

theorem monotonicityCounterEarlyTail_ge_floor :
    monotonicityCounterTailPhaseFloor ≤
      monotonicityCounterDelta +
        monotonicityCounterEarlyTime * monotonicityCounterTail := by
  have hpi := Real.pi_gt_d6
  have hW := monotonicityCounterTail_lower
  have hW0 := monotonicityCounterTail_nonneg
  have hFloorW : monotonicityCounterTailFloor ≤ monotonicityCounterTail := by
    simpa [monotonicityCounterTailFloor] using hW
  have hFloor0 : 0 ≤ monotonicityCounterTailFloor := by
    norm_num [monotonicityCounterTailFloor]
  unfold monotonicityCounterTailPhaseFloor monotonicityCounterEarlyTime
  have hs :
      2 * (3141592 / 1000000 : ℝ) - monotonicityCounterDelta ≤
        2 * Real.pi - monotonicityCounterDelta := by linarith
  have hs0 : 0 ≤
      2 * (3141592 / 1000000 : ℝ) - monotonicityCounterDelta := by
    norm_num [monotonicityCounterDelta]
  have hsUpper0 : 0 ≤ 2 * Real.pi - monotonicityCounterDelta := by
    norm_num [monotonicityCounterDelta]
    nlinarith [Real.pi_gt_three]
  have hmul := mul_le_mul hs hFloorW hFloor0 hsUpper0
  linarith

/-- Early residual phase has a certified cubic chord margin above `4ε`. -/
theorem monotonicityCounterEarlyTail_sub_cube_gt :
    4 * monotonicityCounterEpsilon <
      (monotonicityCounterDelta +
          monotonicityCounterEarlyTime * monotonicityCounterTail) -
        (monotonicityCounterDelta +
          monotonicityCounterEarlyTime * monotonicityCounterTail) ^ (3 : ℕ) / 24 := by
  have hfloor := monotonicityCounterEarlyTail_ge_floor
  have hfloor0 := monotonicityCounterTailPhaseFloor_pos.le
  have hlate := monotonicityCounterLateTail_lt_fourEpsilon
  have htailUpper :
      monotonicityCounterDelta +
          monotonicityCounterEarlyTime * monotonicityCounterTail < 1 := by
    have htime : monotonicityCounterEarlyTime < monotonicityCounterLateTime := by
      unfold monotonicityCounterEarlyTime monotonicityCounterLateTime monotonicityCounterDelta
      norm_num
    have htime0 : 0 < monotonicityCounterEarlyTime := by
      unfold monotonicityCounterEarlyTime monotonicityCounterDelta
      nlinarith [Real.pi_gt_three]
    have hprod := mul_le_mul_of_nonneg_right htime.le monotonicityCounterTail_nonneg
    unfold monotonicityCounterLateTime at hprod
    unfold monotonicityCounterLateTime monotonicityCounterEpsilon at hlate
    unfold monotonicityCounterDelta at ⊢
    nlinarith
  have hmono := sub_cube_div_twentyfour_mono_on_unit hfloor0 hfloor htailUpper.le
  linarith [monotonicityCounterTailPhaseFloor_sub_cube_gt]

noncomputable def monotonicityCounterTotalNonfirstMass : ℝ :=
  (∑ n ∈ Finset.Ioc 1 monotonicityCounterLength, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) +
    ∑ n ∈ Finset.Ioc 1 monotonicityCounterLength, (1 : ℝ) / (n : ℝ) ^ (4 : ℕ)

theorem monotonicityCounterTotalNonfirstMass_upper :
    monotonicityCounterTotalNonfirstMass ≤
      (∑ n ∈ Finset.Ioc (1 : ℕ) 10, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) +
        ((1 : ℝ) / 10 - 1 / 16384) +
      ((∑ n ∈ Finset.Ioc (1 : ℕ) 5, (1 : ℝ) / (n : ℝ) ^ (4 : ℕ)) +
        ((1 : ℝ) / 5 ^ (3 : ℕ) - 1 / 16384 ^ (3 : ℕ))) := by
  have hsTail := sum_inv_sq_Ioc_le 10 (by omega) 16384 (by omega)
  have hbTail := sum_inv_fourth_Ioc_le 5 (by omega) 16384 (by omega)
  have hsSplit := Finset.sum_Ioc_consecutive
    (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) (by omega : 1 ≤ 10) (by omega : 10 ≤ 16384)
  have hbSplit := Finset.sum_Ioc_consecutive
    (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (4 : ℕ)) (by omega : 1 ≤ 5) (by omega : 5 ≤ 16384)
  unfold monotonicityCounterTotalNonfirstMass monotonicityCounterLength
  rw [← hsSplit, ← hbSplit]
  have hsAll :
      (∑ n ∈ Finset.Ioc (1 : ℕ) 10, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) +
          ∑ n ∈ Finset.Ioc (10 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ) ≤
        (∑ n ∈ Finset.Ioc (1 : ℕ) 10, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) +
          ((1 : ℝ) / 10 - 1 / 16384) := by linarith
  have hbAll :
      (∑ n ∈ Finset.Ioc (1 : ℕ) 5, (1 : ℝ) / (n : ℝ) ^ (4 : ℕ)) +
          ∑ n ∈ Finset.Ioc (5 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (4 : ℕ) ≤
        (∑ n ∈ Finset.Ioc (1 : ℕ) 5, (1 : ℝ) / (n : ℝ) ^ (4 : ℕ)) +
          ((1 : ℝ) / 5 ^ (3 : ℕ) - 1 / 16384 ^ (3 : ℕ)) := by linarith
  exact add_le_add hsAll hbAll

/-- Total folded phase at the early time is below `3π/2`, so no second winding is possible. -/
theorem monotonicityCounterTotalPhase_lt_threePiOverTwo :
    monotonicityCounterDelta +
        monotonicityCounterEarlyTime * monotonicityCounterTotalNonfirstMass <
      3 * Real.pi / 2 := by
  have hmass := monotonicityCounterTotalNonfirstMass_upper
  have hpiLo := Real.pi_gt_d6
  have hpiHi := Real.pi_lt_d6
  have htime0 : 0 < monotonicityCounterEarlyTime := by
    unfold monotonicityCounterEarlyTime monotonicityCounterDelta
    nlinarith [Real.pi_gt_three]
  have hmul := mul_le_mul_of_nonneg_left hmass htime0.le
  unfold monotonicityCounterEarlyTime monotonicityCounterDelta at hmul ⊢
  norm_num [Finset.sum_Ioc_succ_top] at hmul ⊢
  nlinarith

theorem monotonicityCounterSmallError :
    4 * monotonicityCounterEpsilon < 1 / 2 := by
  norm_num [monotonicityCounterEpsilon]

theorem monotonicityCounterWindow :
    1024 * Real.pi * monotonicityCounterEpsilon ≤ monotonicityCounterEarlyTime ∧
      monotonicityCounterEarlyTime < monotonicityCounterLateTime ∧
      monotonicityCounterLateTime ≤
        monotonicityCounterEpsilon * monotonicityCounterLength / 2 := by
  unfold monotonicityCounterEpsilon monotonicityCounterEarlyTime
    monotonicityCounterLateTime monotonicityCounterDelta monotonicityCounterLength
  constructor
  · norm_num
    linarith [Real.pi_gt_three]
  constructor
  · norm_num
  · norm_num
    linarith [Real.pi_lt_four]

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
