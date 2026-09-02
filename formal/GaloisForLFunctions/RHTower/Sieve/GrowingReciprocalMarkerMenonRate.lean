import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerBlockCount

/-!
# Rate arithmetic for the growing reciprocal-marker schedule

The growing-marker card needs Menon's mean-square bound to be `o(1 / log X)`.  This module
formalizes the separate, unconditional schedule calculation behind equations `(14)`--`(17)`.

For `w=(log X)^(2/3)` and `h=exp(log X / log log X)`, both normalized error profiles tend to zero:

* `log X * (log w)^2 / w^2` for the shortest retained cofactor window;
* `log X * (log log X)^4 / (log X / 2 - log h + w)^2` for the smallest start scale.

No mean-square estimate is asserted here.  The results verify exactly that the card's chosen scales
would turn its stated Menon bound into `o(1 / log X)`.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- `log X` times the short-window component of Menon's stated rate, at the retained scale `w`. -/
def growingReciprocalMarkerMenonShortRate (x : ℝ) : ℝ :=
  Real.log x * (Real.log (growingReciprocalMarkerW x)) ^ 2 /
    (growingReciprocalMarkerW x) ^ 2

/-- The exact lower logarithmic start scale from equation `(14)`, before its bounded floor error. -/
def growingReciprocalMarkerStartLogLower (x : ℝ) : ℝ :=
  Real.log x / 2 - Real.log (growingReciprocalMarkerH x) + growingReciprocalMarkerW x

/-- `log X` times the start-scale component of Menon's stated rate. -/
def growingReciprocalMarkerMenonStartRate (x : ℝ) : ℝ :=
  Real.log x * (Real.log (Real.log x)) ^ 4 /
    (growingReciprocalMarkerStartLogLower x) ^ 2

/-- Combined normalized rate profile corresponding to equation `(17)`. -/
def growingReciprocalMarkerMenonRate (x : ℝ) : ℝ :=
  growingReciprocalMarkerMenonShortRate x + growingReciprocalMarkerMenonStartRate x

private theorem tendsto_growingReciprocalMarkerW_div_log :
    Tendsto (fun x : ℝ => growingReciprocalMarkerW x / Real.log x) atTop (𝓝 0) := by
  have hlim := tendsto_growingReciprocalMarkerW_div_logH.mul
    tendsto_log_growingReciprocalMarkerH_div_log
  simp only [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
  have hx1 : 1 < x := lt_trans (by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hx
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have hloglogx : Real.log (Real.log x) ≠ 0 := by
    have : 1 < Real.log x := (Real.lt_log_iff_exp_lt (by positivity)).2 hx
    exact ne_of_gt (Real.log_pos this)
  rw [log_growingReciprocalMarkerH]
  field_simp

/-- The smallest retained start has logarithmic scale `(1/2+o(1)) log X`. -/
theorem tendsto_growingReciprocalMarkerStartLogLower_div_log :
    Tendsto (fun x : ℝ => growingReciprocalMarkerStartLogLower x / Real.log x)
      atTop (𝓝 ((1 : ℝ) / 2)) := by
  have hhalf : Tendsto (fun _x : ℝ => ((1 : ℝ) / 2)) atTop (𝓝 ((1 : ℝ) / 2)) :=
    tendsto_const_nhds
  have hlim := (hhalf.sub tendsto_log_growingReciprocalMarkerH_div_log).add
    tendsto_growingReciprocalMarkerW_div_log
  simp only [sub_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [growingReciprocalMarkerStartLogLower]
  field_simp

/-- The shortest-window component of `R_k log X` tends to zero. -/
theorem tendsto_growingReciprocalMarkerMenonShortRate :
    Tendsto growingReciprocalMarkerMenonShortRate atTop (𝓝 0) := by
  let a : ℝ → ℝ := fun x =>
    Real.sqrt (Real.log x) * (Real.log (Real.log x)) ^ 2 /
      growingReciprocalMarkerW x
  have ha : Tendsto a atTop (𝓝 0) :=
    tendsto_sqrtLog_mul_logLog_sq_div_growingReciprocalMarkerW
  have ha2 := ha.mul ha
  simp only [mul_zero] at ha2
  refine squeeze_zero_norm' ?_ ha2
  filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1))] with x hx
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hxe : Real.exp 1 < x := lt_trans (Real.exp_lt_exp.mpr he) hx
  have hx1 : 1 < x := lt_trans he hxe
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hllx1 : 1 < Real.log (Real.log x) :=
    (Real.lt_log_iff_exp_lt (by positivity)).2
      ((Real.lt_log_iff_exp_lt (by positivity)).2 hx)
  have hw : 0 < growingReciprocalMarkerW x := growingReciprocalMarkerW_pos hx1
  have hlogw : Real.log (growingReciprocalMarkerW x) =
      ((2 : ℝ) / 3) * Real.log (Real.log x) := by
    rw [growingReciprocalMarkerW, Real.log_rpow hlx]
  have hrate0 : 0 ≤ growingReciprocalMarkerMenonShortRate x := by
    rw [growingReciprocalMarkerMenonShortRate]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hrate0, growingReciprocalMarkerMenonShortRate, hlogw]
  have hnum : Real.log x * (((2 : ℝ) / 3) * Real.log (Real.log x)) ^ 2 ≤
      Real.log x * (Real.log (Real.log x)) ^ 4 := by
    have ht0 : 0 ≤ Real.log (Real.log x) := le_trans (by norm_num) hllx1.le
    have ht2 : 1 ≤ (Real.log (Real.log x)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (Real.log x) - 1)]
    have ht24 : (Real.log (Real.log x)) ^ 2 ≤ (Real.log (Real.log x)) ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg (Real.log (Real.log x)))]
    nlinarith
  calc
    Real.log x * (((2 : ℝ) / 3) * Real.log (Real.log x)) ^ 2 /
        growingReciprocalMarkerW x ^ 2
        ≤ Real.log x * (Real.log (Real.log x)) ^ 4 /
          growingReciprocalMarkerW x ^ 2 := by
            exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = a x * a x := by
      dsimp [a]
      rw [div_mul_div_comm]
      field_simp [ne_of_gt hw]
      nlinarith [Real.sq_sqrt hlx.le]

/-- The moving-start component of `R_k log X` tends to zero. -/
theorem tendsto_growingReciprocalMarkerMenonStartRate :
    Tendsto growingReciprocalMarkerMenonStartRate atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ =>
      (Real.log (Real.log x)) ^ 4 / Real.log x) atTop (𝓝 0) := by
    have hraw := RHTower.tendsto_logLog_rpow_div_log_rpow (4 : ℝ)
      (s := (1 : ℝ)) (by norm_num)
    refine hraw.congr' (Filter.Eventually.of_forall fun x => ?_)
    change Real.log (Real.log x) ^ (4 : ℝ) / Real.log x ^ (1 : ℝ) =
      Real.log (Real.log x) ^ (4 : ℕ) / Real.log x
    have hp4 : Real.log (Real.log x) ^ (4 : ℝ) =
        Real.log (Real.log x) ^ (4 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log (Real.log x)) 4
    rw [hp4, Real.rpow_one]
  have hupper := hbase.const_mul (16 : ℝ)
  simp only [mul_zero] at hupper
  refine squeeze_zero_norm' ?_ hupper
  have hquarter : (1 : ℝ) / 4 < (1 : ℝ) / 2 := by norm_num
  filter_upwards [
    tendsto_growingReciprocalMarkerStartLogLower_div_log.eventually_const_lt hquarter,
    eventually_gt_atTop (Real.exp 1)] with x hratio hx
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hx1 : 1 < x := lt_trans he hx
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hratio0 : 0 < growingReciprocalMarkerStartLogLower x / Real.log x :=
    lt_trans (by norm_num) hratio
  have hstart : 0 < growingReciprocalMarkerStartLogLower x := by
    have := mul_pos hratio0 hlx
    rw [div_mul_cancel₀ _ (ne_of_gt hlx)] at this
    exact this
  have hrate0 : 0 ≤ growingReciprocalMarkerMenonStartRate x := by
    rw [growingReciprocalMarkerMenonStartRate]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hrate0]
  have heq : growingReciprocalMarkerMenonStartRate x =
      ((Real.log (Real.log x)) ^ 4 / Real.log x) /
        (growingReciprocalMarkerStartLogLower x / Real.log x) ^ 2 := by
    rw [growingReciprocalMarkerMenonStartRate]
    field_simp
  rw [heq]
  have hden : (1 : ℝ) / 16 <
      (growingReciprocalMarkerStartLogLower x / Real.log x) ^ 2 := by
    nlinarith
  have hbase0 : 0 ≤ (Real.log (Real.log x)) ^ 4 / Real.log x := by positivity
  rw [div_le_iff₀ (by linarith : 0 <
      (growingReciprocalMarkerStartLogLower x / Real.log x) ^ 2)]
  nlinarith

/-- The complete normalized rate profile in equation `(17)` tends to zero. -/
theorem tendsto_growingReciprocalMarkerMenonRate :
    Tendsto growingReciprocalMarkerMenonRate atTop (𝓝 0) := by
  change Tendsto (fun x => growingReciprocalMarkerMenonShortRate x +
    growingReciprocalMarkerMenonStartRate x) atTop (𝓝 0)
  simpa only [zero_add] using tendsto_growingReciprocalMarkerMenonShortRate.add
    tendsto_growingReciprocalMarkerMenonStartRate

end

end RHTower.Sieve
