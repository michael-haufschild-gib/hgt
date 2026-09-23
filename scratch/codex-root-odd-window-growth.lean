import GaloisForLFunctions.RHTower.MassBesselRadiationDivergence

namespace RHTower

/-- Critical-Mellin PNT main scale dominates every logarithmic separator
debit on fixed multiplicative windows. -/
theorem tendsto_odd_window_main_minus_log_atTop
    {a K : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun x : ℝ => a * Real.sqrt x / Real.log x -
        2 * (Real.log K + Real.log x) - Real.log 2)
      Filter.atTop Filter.atTop := by
  have hratio : Filter.Tendsto
      (fun x : ℝ => a * (Real.sqrt x / Real.log x ^ (2 : ℕ)))
      Filter.atTop Filter.atTop :=
    (tendsto_sqrt_div_log_pow_atTop 2).const_mul_atTop ha
  have hfactor : Filter.Tendsto
      (fun x : ℝ => a * (Real.sqrt x / Real.log x ^ (2 : ℕ)) - 2)
      Filter.atTop Filter.atTop :=
    hratio.atTop_add (tendsto_const_nhds (x := (-2 : ℝ)))
  have hlog : Filter.Tendsto Real.log Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop
  have hprod : Filter.Tendsto
      (fun x : ℝ => Real.log x *
        (a * (Real.sqrt x / Real.log x ^ (2 : ℕ)) - 2))
      Filter.atTop Filter.atTop :=
    hlog.atTop_mul_atTop₀ hfactor
  have hrest : Filter.Tendsto
      (fun _x : ℝ => -2 * Real.log K - Real.log 2)
      Filter.atTop (nhds (-2 * Real.log K - Real.log 2)) :=
    tendsto_const_nhds
  have hsum := hprod.atTop_add hrest
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hlogne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  change Real.log x *
      (a * (Real.sqrt x / Real.log x ^ (2 : ℕ)) - 2) +
        (-2 * Real.log K - Real.log 2) =
      a * Real.sqrt x / Real.log x -
        2 * (Real.log K + Real.log x) - Real.log 2
  field_simp [hlogne]
  ring

end RHTower
