import GaloisForLFunctions.RHTower.Sieve.ShortIntervalLength

/-!
# The iterated logarithm against a power of the logarithm

The truncation depth of the sieve is of size `log log x`, while the level constraint has room
`(log x)^{1−β}`.  The two are compared by the standard fact that a logarithm is little-o of any
positive power.
-/

namespace RHTower.Sieve

open Filter Topology Asymptotics

/-- **A logarithm is dominated by any positive power.** -/
theorem tendsto_log_div_rpow {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => Real.log t / t ^ δ) atTop (𝓝 0) := by
  have hlo : (fun t : ℝ => Real.log t) =o[atTop] (fun t : ℝ => t ^ δ) :=
    isLittleO_log_rpow_atTop hδ
  have hne : ∀ᶠ t : ℝ in atTop, t ^ δ ≠ 0 := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact ne_of_gt (Real.rpow_pos_of_pos ht δ)
  exact hlo.tendsto_div_nhds_zero

/-- **The iterated logarithm is small against a power of the logarithm.**  This is the comparison
that makes the sieve's truncation depth affordable inside the level constraint. -/
theorem tendsto_logLog_div_logRpow {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => Real.log (Real.log x) / (Real.log x) ^ δ) atTop (𝓝 0) :=
  (tendsto_log_div_rpow hδ).comp Real.tendsto_log_atTop

end RHTower.Sieve
