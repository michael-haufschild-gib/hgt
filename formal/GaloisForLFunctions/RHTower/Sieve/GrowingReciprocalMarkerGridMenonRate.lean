import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerLengthGrid
import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerMenonRate

open Filter Topology

namespace RHTower.Sieve

noncomputable section

private theorem tendsto_logLog_cube_div_log_third :
    Tendsto (fun x : ℝ =>
      (Real.log (Real.log x)) ^ 3 / (Real.log x) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
  have hraw := RHTower.tendsto_logLog_rpow_div_log_rpow (3 : ℝ)
    (s := ((1 : ℝ) / 3)) (by norm_num)
  refine hraw.congr' (Filter.Eventually.of_forall fun x => ?_)
  have hp3 : Real.log (Real.log x) ^ (3 : ℝ) =
      Real.log (Real.log x) ^ (3 : ℕ) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log (Real.log x)) 3
  rw [hp3]

private theorem tendsto_logLog_fifth_div_log :
    Tendsto (fun x : ℝ =>
      (Real.log (Real.log x)) ^ 5 / Real.log x) atTop (𝓝 0) := by
  have hraw := RHTower.tendsto_logLog_rpow_div_log_rpow (5 : ℝ)
    (s := (1 : ℝ)) (by norm_num)
  refine hraw.congr' (Filter.Eventually.of_forall fun x => ?_)
  have hp5 : Real.log (Real.log x) ^ (5 : ℝ) =
      Real.log (Real.log x) ^ (5 : ℕ) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log (Real.log x)) 5
  rw [hp5, Real.rpow_one]

/-- The `ceil(log log X)` normalization breadth preserves the rate required in equation `(17)`. -/
theorem tendsto_growingReciprocalMarkerGridBreadth_mul_menonRate :
    Tendsto (fun x : ℝ =>
      (growingReciprocalMarkerGridBreadth x : ℝ) *
        growingReciprocalMarkerMenonRate x) atTop (𝓝 0) := by
  have hshortMajor := tendsto_logLog_cube_div_log_third.const_mul (2 : ℝ)
  simp only [mul_zero] at hshortMajor
  have hstartMajor := tendsto_logLog_fifth_div_log.const_mul (32 : ℝ)
  simp only [mul_zero] at hstartMajor
  have hmajor := hshortMajor.add hstartMajor
  simp only [zero_add] at hmajor
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1))] with x hx
    have he : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    have hxe : Real.exp 1 < x := lt_trans (Real.exp_lt_exp.mpr he) hx
    have hx1 : 1 < x := lt_trans he hxe
    have hlx : 0 < Real.log x := Real.log_pos hx1
    have hw : 0 < growingReciprocalMarkerW x := growingReciprocalMarkerW_pos hx1
    rw [growingReciprocalMarkerMenonRate, growingReciprocalMarkerMenonShortRate,
      growingReciprocalMarkerMenonStartRate]
    positivity
  · filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1)),
      tendsto_growingReciprocalMarkerStartLogLower_div_log.eventually_const_lt
        (by norm_num : (1 : ℝ) / 4 < (1 : ℝ) / 2)] with x hx hratio
    have he : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    have hxe : Real.exp 1 < x := lt_trans (Real.exp_lt_exp.mpr he) hx
    have hx1 : 1 < x := lt_trans he hxe
    have hlx : 0 < Real.log x := Real.log_pos hx1
    have ht1 : 1 < Real.log (Real.log x) :=
      (Real.lt_log_iff_exp_lt (by positivity)).2
        ((Real.lt_log_iff_exp_lt (by positivity)).2 hx)
    have ht0 : 0 ≤ Real.log (Real.log x) := ht1.le.trans' (by norm_num)
    have hKceil : (growingReciprocalMarkerGridBreadth x : ℝ)
        < Real.log (Real.log x) + 1 := by
      exact Nat.ceil_lt_add_one ht0
    have hK : (growingReciprocalMarkerGridBreadth x : ℝ)
        ≤ 2 * Real.log (Real.log x) := by linarith
    have hw : 0 < growingReciprocalMarkerW x := growingReciprocalMarkerW_pos hx1
    have hlogw : Real.log (growingReciprocalMarkerW x) =
        ((2 : ℝ) / 3) * Real.log (Real.log x) := by
      rw [growingReciprocalMarkerW, Real.log_rpow hlx]
    have hKt2 : (growingReciprocalMarkerGridBreadth x : ℝ) *
        (Real.log (Real.log x)) ^ 2 ≤ 2 * (Real.log (Real.log x)) ^ 3 := by
      have hm := mul_le_mul_of_nonneg_right hK (sq_nonneg (Real.log (Real.log x)))
      nlinarith
    have hnumShort : (growingReciprocalMarkerGridBreadth x : ℝ) *
          (Real.log x * (((2 : ℝ) / 3) * Real.log (Real.log x)) ^ 2)
        ≤ 2 * Real.log x * (Real.log (Real.log x)) ^ 3 := by
      have hm := mul_le_mul_of_nonneg_left hKt2 hlx.le
      nlinarith
    have hshort : (growingReciprocalMarkerGridBreadth x : ℝ) *
          growingReciprocalMarkerMenonShortRate x
        ≤ 2 * Real.log x * (Real.log (Real.log x)) ^ 3 /
            growingReciprocalMarkerW x ^ 2 := by
      rw [growingReciprocalMarkerMenonShortRate, hlogw]
      calc
        (growingReciprocalMarkerGridBreadth x : ℝ) *
            (Real.log x * (((2 : ℝ) / 3) * Real.log (Real.log x)) ^ 2 /
              growingReciprocalMarkerW x ^ 2)
          = ((growingReciprocalMarkerGridBreadth x : ℝ) *
              (Real.log x * (((2 : ℝ) / 3) * Real.log (Real.log x)) ^ 2)) /
                growingReciprocalMarkerW x ^ 2 := by ring
        _ ≤ 2 * Real.log x * (Real.log (Real.log x)) ^ 3 /
              growingReciprocalMarkerW x ^ 2 :=
          div_le_div_of_nonneg_right hnumShort (sq_nonneg _)
    have hwSq : growingReciprocalMarkerW x ^ 2 =
        (Real.log x) ^ ((4 : ℝ) / 3) := by
      rw [growingReciprocalMarkerW]
      calc
        ((Real.log x) ^ ((2 : ℝ) / 3)) ^ (2 : ℕ) =
            ((Real.log x) ^ ((2 : ℝ) / 3)) ^ (2 : ℝ) := by
          exact (Real.rpow_natCast ((Real.log x) ^ ((2 : ℝ) / 3)) 2).symm
        _ = (Real.log x) ^ (((2 : ℝ) / 3) * 2) := by
          rw [Real.rpow_mul hlx.le]
        _ = (Real.log x) ^ ((4 : ℝ) / 3) := by norm_num
    have hpowSplit : (Real.log x) ^ ((4 : ℝ) / 3) =
        Real.log x * (Real.log x) ^ ((1 : ℝ) / 3) := by
      calc
        (Real.log x) ^ ((4 : ℝ) / 3) =
            (Real.log x) ^ ((1 : ℝ) + (1 : ℝ) / 3) := by norm_num
        _ = (Real.log x) ^ (1 : ℝ) * (Real.log x) ^ ((1 : ℝ) / 3) :=
          Real.rpow_add hlx 1 ((1 : ℝ) / 3)
        _ = Real.log x * (Real.log x) ^ ((1 : ℝ) / 3) := by rw [Real.rpow_one]
    have hshortEq : 2 * Real.log x * (Real.log (Real.log x)) ^ 3 /
          growingReciprocalMarkerW x ^ 2 =
        2 * ((Real.log (Real.log x)) ^ 3 /
          (Real.log x) ^ ((1 : ℝ) / 3)) := by
      rw [hwSq, hpowSplit]
      field_simp [ne_of_gt hlx, ne_of_gt (Real.rpow_pos_of_pos hlx _)]
    have hstartPos : 0 < growingReciprocalMarkerStartLogLower x := by
      have hratio0 : 0 < growingReciprocalMarkerStartLogLower x / Real.log x :=
        lt_trans (by norm_num) hratio
      have := mul_pos hratio0 hlx
      rw [div_mul_cancel₀ _ (ne_of_gt hlx)] at this
      exact this
    have hstartLower : Real.log x / 4 < growingReciprocalMarkerStartLogLower x := by
      have hm := (lt_div_iff₀ hlx).1 hratio
      nlinarith
    have hstartSqLower : (Real.log x) ^ 2 / 16 ≤
        growingReciprocalMarkerStartLogLower x ^ 2 := by
      nlinarith [sq_nonneg (growingReciprocalMarkerStartLogLower x - Real.log x / 4)]
    have hKt4 : (growingReciprocalMarkerGridBreadth x : ℝ) *
        (Real.log (Real.log x)) ^ 4 ≤ 2 * (Real.log (Real.log x)) ^ 5 := by
      have hm := mul_le_mul_of_nonneg_right hK
        (by positivity : 0 ≤ (Real.log (Real.log x)) ^ 4)
      nlinarith
    have hnumStart : (growingReciprocalMarkerGridBreadth x : ℝ) *
          (Real.log x * (Real.log (Real.log x)) ^ 4)
        ≤ 2 * Real.log x * (Real.log (Real.log x)) ^ 5 := by
      have hm := mul_le_mul_of_nonneg_left hKt4 hlx.le
      nlinarith
    have hstart1 : (growingReciprocalMarkerGridBreadth x : ℝ) *
          growingReciprocalMarkerMenonStartRate x
        ≤ 2 * Real.log x * (Real.log (Real.log x)) ^ 5 /
            growingReciprocalMarkerStartLogLower x ^ 2 := by
      rw [growingReciprocalMarkerMenonStartRate]
      calc
        (growingReciprocalMarkerGridBreadth x : ℝ) *
            (Real.log x * (Real.log (Real.log x)) ^ 4 /
              growingReciprocalMarkerStartLogLower x ^ 2)
          = ((growingReciprocalMarkerGridBreadth x : ℝ) *
              (Real.log x * (Real.log (Real.log x)) ^ 4)) /
                growingReciprocalMarkerStartLogLower x ^ 2 := by ring
        _ ≤ 2 * Real.log x * (Real.log (Real.log x)) ^ 5 /
              growingReciprocalMarkerStartLogLower x ^ 2 :=
          div_le_div_of_nonneg_right hnumStart (sq_nonneg _)
    have hstart2 : 2 * Real.log x * (Real.log (Real.log x)) ^ 5 /
          growingReciprocalMarkerStartLogLower x ^ 2
        ≤ 2 * Real.log x * (Real.log (Real.log x)) ^ 5 /
            ((Real.log x) ^ 2 / 16) := by
      exact div_le_div_of_nonneg_left (by positivity)
        (by positivity) hstartSqLower
    have hstartEq : 2 * Real.log x * (Real.log (Real.log x)) ^ 5 /
          ((Real.log x) ^ 2 / 16) =
        32 * ((Real.log (Real.log x)) ^ 5 / Real.log x) := by
      field_simp [ne_of_gt hlx]
      norm_num
    rw [growingReciprocalMarkerMenonRate, mul_add]
    rw [← hshortEq, ← hstartEq]
    exact add_le_add hshort (hstart1.trans hstart2)

end

end RHTower.Sieve
