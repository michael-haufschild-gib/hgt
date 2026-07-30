import Mathlib

/-!
# Analytic order rigidity from asymptotic onset

An analytic function that is `O (‖g‖ ^ r)` cannot have a nonzero Taylor
coefficient below order `r`. This closes the exact bridge from geometric
Big-O locality bounds to intrinsic analytic birth valuation.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Analytic unit obtained after removing the exact series-order monomial. -/
private def analyticOrderUnit
    (f : ℂ → ℂ)
    (series : FormalMultilinearSeries ℂ ℂ ℂ) : ℂ → ℂ :=
  (Function.swap dslope 0)^[series.order] f

private theorem analyticOrderUnit_zero_ne
    {f : ℂ → ℂ}
    {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hseries : series ≠ 0) :
    analyticOrderUnit f series 0 ≠ 0 := by
  exact hf.iterate_dslope_fslope_ne_zero hseries

private theorem analyticOrderUnit_continuousAt
    {f : ℂ → ℂ}
    {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0) :
    ContinuousAt (analyticOrderUnit f series) 0 := by
  exact
    (hf.has_fpower_series_iterate_dslope_fslope
      series.order).analyticAt.continuousAt

private theorem analytic_eq_pow_order_mul_unit
    {f : ℂ → ℂ}
    {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (g : ℂ) :
    f g =
      g ^ series.order *
        analyticOrderUnit f series g := by
  simpa [analyticOrderUnit, smul_eq_mul] using
    hf.eq_pow_order_mul_iterate_dslope g

private theorem tendsto_norm_div_norm_pow_order
    {f : ℂ → ℂ}
    {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0) :
    Tendsto
      (fun g : ℂ =>
        ‖f g‖ / ‖g‖ ^ series.order)
      (𝓝[≠] 0)
      (𝓝 ‖analyticOrderUnit f series 0‖) := by
  have hunit :
      Tendsto
        (fun g : ℂ =>
          ‖analyticOrderUnit f series g‖)
        (𝓝[≠] 0)
        (𝓝 ‖analyticOrderUnit f series 0‖) :=
    (analyticOrderUnit_continuousAt hf).norm.mono_left
      inf_le_left
  apply hunit.congr'
  filter_upwards [self_mem_nhdsWithin] with g hg
  have hg0 : g ≠ 0 := by
    simpa using hg
  rw [analytic_eq_pow_order_mul_unit hf,
    norm_mul, norm_pow]
  exact
    (mul_div_cancel_left₀ _
      (pow_ne_zero _
        (norm_ne_zero_iff.mpr hg0))).symm

/-- **Analytic onset rigidity.** A nonzero analytic series representing a
function with onset `O (‖g‖ ^ r)` has exact Taylor order at least `r`. -/
theorem le_fpowerSeries_order_of_isBigO_norm_pow
    {f : ℂ → ℂ}
    {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hseries : series ≠ 0)
    (r : ℕ)
    (hO : f =O[𝓝 0] fun g : ℂ => ‖g‖ ^ r) :
    r ≤ series.order := by
  by_contra hnot
  have hlt : series.order < r := by
    omega
  have hlittle :
      f =o[𝓝 0]
        (fun g : ℂ => ‖g‖ ^ series.order) :=
    hO.trans_isLittleO
      (isLittleO_norm_pow_norm_pow hlt)
  have hlead :=
    tendsto_norm_div_norm_pow_order hf
  have hlead0 :
      ‖analyticOrderUnit f series 0‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (analyticOrderUnit_zero_ne hf hseries)
  have hreverse :
      (fun g : ℂ => ‖g‖ ^ series.order)
        =O[𝓝[≠] 0] fun g => ‖f g‖ :=
    isBigO_of_div_tendsto_nhds_of_ne_zero
      hlead hlead0
  have hlittle' :
      f =o[𝓝[≠] 0]
        (fun g : ℂ => ‖g‖ ^ series.order) :=
    hlittle.mono inf_le_left
  have hfreq :
      ∃ᶠ g in 𝓝[≠] (0 : ℂ),
        ‖g‖ ^ series.order ≠ 0 := by
    have hev :
        ∀ᶠ g in 𝓝[≠] (0 : ℂ),
          ‖g‖ ^ series.order ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with g hg
      exact
        pow_ne_zero _
          (norm_ne_zero_iff.mpr (by simpa using hg))
    exact hev.frequently
  exact
    (hreverse.not_isLittleO hfreq)
      hlittle'.norm_left

end

end GaloisForLFunctions.HTGeometry
