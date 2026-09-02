import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerBlockCount

/-!
# Aggregate capacity scale for growing reciprocal markers

Equation `(30)` of the growing reciprocal-marker card supplies the scale `H / log X` in every
retained dyadic block.  Equation `(10)` retains asymptotically `log h / log 2` blocks.  This module
performs that final schedule aggregation without suppressing the constant: on the card's exact
choice `h(X) = exp(log X / log log X)`, the aggregate per-block scale divided by
`H / log log X` tends to `1 / log 2`.

This is the analytic-free arithmetic passage from `(30)` to `(7)`.  It asserts no Möbius or prime
supply estimate.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- **Exact aggregation of the card's per-block capacity scale.**  Summing one copy of
`H / log X` over the exact retained-block count has asymptotic scale
`H / (log 2 * log log X)`. -/
theorem tendsto_growingReciprocalMarker_aggregateBlockScale :
    Tendsto (fun x : ℝ =>
      ((growingReciprocalMarkerBlockCount x : ℝ) *
          (growingReciprocalMarkerWindow x / Real.log x)) /
        (growingReciprocalMarkerWindow x / Real.log (Real.log x)))
      atTop (𝓝 (1 / Real.log 2)) := by
  refine tendsto_growingReciprocalMarkerBlockCount_div_logH.congr' ?_
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
  have hx1 : 1 < x := lt_trans (by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hx
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have hloglogx : Real.log (Real.log x) ≠ 0 := by
    have hlogone : 1 < Real.log x := (Real.lt_log_iff_exp_lt (by positivity)).2 hx
    exact ne_of_gt (Real.log_pos hlogone)
  have hwindow : growingReciprocalMarkerWindow x ≠ 0 := by
    rw [growingReciprocalMarkerWindow]
    exact mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by linarith)))
      (ne_of_gt (growingReciprocalMarkerH_pos x))
  rw [log_growingReciprocalMarkerH]
  field_simp

end


end RHTower.Sieve
