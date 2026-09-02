import GaloisForLFunctions.RHTower.MobiusSparseForbiddenDeletion

/-!
# Near-maximal subpower schedule for growing reciprocal markers

This formalizes the card's concrete schedule
\`h(X)=exp(log X / log log X)\`, \`w(X)=(log X)^(2/3)\`, and
\`H(X)=sqrt X * h(X)\`.  It proves exactly the three scale relations used by the growing-block
argument and the logarithmic statement \`H=X^(1/2+o(1))\`.  These are unconditional asymptotic
facts; no Möbius mean-square estimate is introduced.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

def growingReciprocalMarkerH (x : ℝ) : ℝ :=
  Real.exp (Real.log x / Real.log (Real.log x))

def growingReciprocalMarkerW (x : ℝ) : ℝ :=
  (Real.log x) ^ ((2 : ℝ) / 3)

def growingReciprocalMarkerWindow (x : ℝ) : ℝ := Real.sqrt x * growingReciprocalMarkerH x

theorem growingReciprocalMarkerH_pos (x : ℝ) : 0 < growingReciprocalMarkerH x := by
  exact Real.exp_pos _

theorem growingReciprocalMarkerW_pos {x : ℝ} (hx : 1 < x) : 0 < growingReciprocalMarkerW x := by
  exact Real.rpow_pos_of_pos (Real.log_pos hx) _

theorem log_growingReciprocalMarkerH (x : ℝ) :
    Real.log (growingReciprocalMarkerH x) = Real.log x / Real.log (Real.log x) := by
  simp [growingReciprocalMarkerH]

theorem tendsto_log_growingReciprocalMarkerH_div_log :
    Tendsto (fun x : ℝ => Real.log (growingReciprocalMarkerH x) / Real.log x) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => (1 : ℝ) / Real.log (Real.log x)) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop) 1
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hx
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hx1 : 1 < x := lt_trans he hx
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hlogone : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt (lt_trans (by positivity) hx)).2 hx
  have hllx : 0 < Real.log (Real.log x) := Real.log_pos hlogone
  rw [log_growingReciprocalMarkerH]
  field_simp

theorem tendsto_sqrtLog_mul_logLog_sq_div_growingReciprocalMarkerW :
    Tendsto (fun x : ℝ =>
      Real.sqrt (Real.log x) * (Real.log (Real.log x)) ^ 2 / growingReciprocalMarkerW x)
      atTop (𝓝 0) := by
  have hlim := RHTower.tendsto_logLog_rpow_div_log_rpow (2 : ℝ)
    (s := (1 : ℝ) / 6) (by norm_num)
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hx
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hx1 : 1 < x := lt_trans he hx
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hlogone : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt (lt_trans (by positivity) hx)).2 hx
  have hllx : 0 < Real.log (Real.log x) := Real.log_pos hlogone
  have hp : (Real.log x) ^ ((1 : ℝ) / 2) *
      (Real.log x) ^ ((1 : ℝ) / 6) =
      (Real.log x) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add hlx]
    congr 1
    ring
  rw [growingReciprocalMarkerW, Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hlx ((1 : ℝ) / 6)),
    ne_of_gt (Real.rpow_pos_of_pos hlx ((2 : ℝ) / 3))]
  rw [mul_comm ((Real.log x) ^ ((1 : ℝ) / 6)), hp,
    Real.rpow_natCast]
  calc
    (Real.log (Real.log x)) ^ (2 : ℝ) * (Real.log x) ^ ((2 : ℝ) / 3) =
        (Real.log (Real.log x)) ^ (2 : ℕ) *
          (Real.log x) ^ ((2 : ℝ) / 3) := by
      exact congrArg (fun z : ℝ => z * (Real.log x) ^ ((2 : ℝ) / 3))
        (Real.rpow_natCast (Real.log (Real.log x)) 2)
    _ = _ := mul_comm _ _

theorem tendsto_growingReciprocalMarkerW_div_logH :
    Tendsto (fun x : ℝ => growingReciprocalMarkerW x / Real.log (growingReciprocalMarkerH x)) atTop (𝓝 0) := by
  have hlim := RHTower.tendsto_logLog_rpow_div_log_rpow (1 : ℝ)
    (s := (1 : ℝ) / 3) (by norm_num)
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hx
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hx1 : 1 < x := lt_trans he hx
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hlogone : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt (lt_trans (by positivity) hx)).2 hx
  have hllx : 0 < Real.log (Real.log x) := Real.log_pos hlogone
  have hp : (Real.log x) ^ ((2 : ℝ) / 3) *
      (Real.log x) ^ ((1 : ℝ) / 3) = Real.log x := by
    rw [← Real.rpow_add hlx]
    norm_num
  rw [growingReciprocalMarkerW, log_growingReciprocalMarkerH, Real.rpow_one]
  field_simp [ne_of_gt hlx, ne_of_gt hllx,
    ne_of_gt (Real.rpow_pos_of_pos hlx ((1 : ℝ) / 3))]
  nlinarith

theorem tendsto_log_growingReciprocalMarkerWindow_div_log_half :
    Tendsto (fun x : ℝ => Real.log (growingReciprocalMarkerWindow x) / Real.log x)
      atTop (𝓝 ((1 : ℝ) / 2)) := by
  have hlim : Tendsto
      (fun x : ℝ => (1 : ℝ) / 2 + Real.log (growingReciprocalMarkerH x) / Real.log x)
      atTop (𝓝 ((1 : ℝ) / 2)) := by
    simpa using (tendsto_const_nhds.add tendsto_log_growingReciprocalMarkerH_div_log)
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hsqrt : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx0)
  have hH : growingReciprocalMarkerH x ≠ 0 := ne_of_gt (growingReciprocalMarkerH_pos x)
  rw [growingReciprocalMarkerWindow, Real.log_mul hsqrt hH, Real.log_sqrt hx0.le]
  field_simp

end

end RHTower.Sieve

