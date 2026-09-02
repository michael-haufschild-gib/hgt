import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerSubpowerSchedule

/-!
# Number of retained growing reciprocal-marker blocks

This module formalizes equation `(10)` of the growing reciprocal-marker card without removing its
floor or truncated natural subtraction.  For the card's exact schedules it proves

`K(x) → ∞` and `K(x) / log h(x) → 1 / log 2`.

Thus the construction has asymptotically `log h / log 2` retained dyadic blocks.  This is the exact
block-count factor used when summing the per-block target supply.
-/

open Filter Topology Asymptotics

namespace RHTower.Sieve

noncomputable section

/-- The real expression inside the floor in equation `(10)`. -/
def growingReciprocalMarkerBlockScale (x : ℝ) : ℝ :=
  (Real.log (growingReciprocalMarkerH x) - growingReciprocalMarkerW x) / Real.log 2

/-- Equation `(10)`, including both the natural floor and subtraction by four. -/
def growingReciprocalMarkerBlockCount (x : ℝ) : ℕ :=
  ⌊growingReciprocalMarkerBlockScale x⌋₊ - 4

private theorem tendsto_id_div_log_atTop :
    Tendsto (fun z : ℝ => z / Real.log z) atTop atTop := by
  have h0 : Tendsto (fun z : ℝ => Real.log z / z) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa only [Real.rpow_one] using
        (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
    exact div_pos (Real.log_pos hz) (by linarith)
  have h1 := tendsto_inv_nhdsGT_zero.comp h0
  refine h1.congr fun z => ?_
  simp only [Function.comp_apply]
  rw [inv_div]

private theorem tendsto_log_growingReciprocalMarkerH_atTop :
    Tendsto (fun x : ℝ => Real.log (growingReciprocalMarkerH x)) atTop atTop := by
  have hlim := tendsto_id_div_log_atTop.comp Real.tendsto_log_atTop
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
  simp only [Function.comp_apply, log_growingReciprocalMarkerH]

/-- Before flooring, the retained-block scale has the claimed logarithmic normalization. -/
theorem tendsto_growingReciprocalMarkerBlockScale_div_logH :
    Tendsto (fun x : ℝ =>
      growingReciprocalMarkerBlockScale x / Real.log (growingReciprocalMarkerH x))
      atTop (𝓝 (1 / Real.log 2)) := by
  have hone : Tendsto (fun _x : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim := (hone.sub tendsto_growingReciprocalMarkerW_div_logH).div_const (Real.log 2)
  simp only [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [tendsto_log_growingReciprocalMarkerH_atTop.eventually_ge_atTop 1] with x hx
  have hne : Real.log (growingReciprocalMarkerH x) ≠ 0 := by linarith
  rw [growingReciprocalMarkerBlockScale]
  field_simp

private theorem tendsto_growingReciprocalMarkerBlockScale_atTop :
    Tendsto growingReciprocalMarkerBlockScale atTop atTop := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < (1 / Real.log 2) / 2 := by positivity
  have hratio := tendsto_growingReciprocalMarkerBlockScale_div_logH.eventually_const_lt
    (by nlinarith [hlog2] : (1 / Real.log 2) / 2 < 1 / Real.log 2)
  have hscaled := tendsto_log_growingReciprocalMarkerH_atTop.const_mul_atTop hc
  rw [tendsto_atTop]
  intro b
  filter_upwards [hratio,
    tendsto_log_growingReciprocalMarkerH_atTop.eventually_ge_atTop 1,
    hscaled.eventually_ge_atTop b] with x hratio hlog hbound
  have heq : growingReciprocalMarkerBlockScale x =
      (growingReciprocalMarkerBlockScale x / Real.log (growingReciprocalMarkerH x)) *
        Real.log (growingReciprocalMarkerH x) := by
    field_simp
  rw [heq]
  nlinarith

/-- Equation `(10)` retains an unbounded number of blocks. -/
theorem tendsto_growingReciprocalMarkerBlockCount_atTop :
    Tendsto growingReciprocalMarkerBlockCount atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [tendsto_growingReciprocalMarkerBlockScale_atTop.eventually_ge_atTop
      ((b : ℝ) + 5)] with x hscale
  let n := ⌊growingReciprocalMarkerBlockScale x⌋₊
  have hlt : growingReciprocalMarkerBlockScale x < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hb : b + 4 < n := by exact_mod_cast (by linarith : (b : ℝ) + 4 < (n : ℝ))
  rw [growingReciprocalMarkerBlockCount]
  change b ≤ n - 4
  omega

/-- Flooring and subtracting four do not change the logarithmic block-count asymptotic. -/
theorem tendsto_growingReciprocalMarkerBlockCount_div_logH :
    Tendsto (fun x : ℝ =>
      (growingReciprocalMarkerBlockCount x : ℝ) /
        Real.log (growingReciprocalMarkerH x))
      atTop (𝓝 (1 / Real.log 2)) := by
  have herr : Tendsto (fun x : ℝ =>
      (growingReciprocalMarkerBlockScale x -
        (growingReciprocalMarkerBlockCount x : ℝ)) /
          Real.log (growingReciprocalMarkerH x)) atTop (𝓝 0) := by
    have hupper := Filter.Tendsto.const_div_atTop
      tendsto_log_growingReciprocalMarkerH_atTop 5
    refine squeeze_zero_norm' ?_ hupper
    filter_upwards [tendsto_growingReciprocalMarkerBlockScale_atTop.eventually_ge_atTop 5,
      tendsto_log_growingReciprocalMarkerH_atTop.eventually_ge_atTop 1] with x hscale hlog
    let n := ⌊growingReciprocalMarkerBlockScale x⌋₊
    have hscale0 : 0 ≤ growingReciprocalMarkerBlockScale x := by linarith
    have hnle : (n : ℝ) ≤ growingReciprocalMarkerBlockScale x := Nat.floor_le hscale0
    have hlt : growingReciprocalMarkerBlockScale x < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hn4real : (4 : ℝ) ≤ (n : ℝ) := by linarith
    have hn4 : 4 ≤ n := by exact_mod_cast hn4real
    have hcount : (growingReciprocalMarkerBlockCount x : ℝ) = (n : ℝ) - 4 := by
      rw [growingReciprocalMarkerBlockCount]
      change (((n - 4 : ℕ) : ℕ) : ℝ) = (n : ℝ) - 4
      exact Nat.cast_sub hn4
    have hdiff0 : 0 ≤ growingReciprocalMarkerBlockScale x -
        (growingReciprocalMarkerBlockCount x : ℝ) := by
      rw [hcount]
      linarith
    have hdiff5 : growingReciprocalMarkerBlockScale x -
        (growingReciprocalMarkerBlockCount x : ℝ) ≤ 5 := by
      rw [hcount]
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hdiff0 (by linarith))]
    exact div_le_div_of_nonneg_right hdiff5 (by linarith)
  have hlim := tendsto_growingReciprocalMarkerBlockScale_div_logH.sub herr
  simp only [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [tendsto_log_growingReciprocalMarkerH_atTop.eventually_ge_atTop 1] with x hlog
  field_simp
  ring

end

end RHTower.Sieve
