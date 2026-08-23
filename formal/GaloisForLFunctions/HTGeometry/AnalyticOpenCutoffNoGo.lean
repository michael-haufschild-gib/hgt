import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic

/-!
# Analytic pointwise cutoffs cannot separate open windows

On a preconnected complex domain, an analytic scalar that vanishes on one
nonempty open region vanishes everywhere.  Hence no analytic pointwise cutoff
can be zero on one nonempty open node window and one on another.  This is the
cutoff obstruction used by Euler/Pick window-localization arguments.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

/-- An analytic scalar that is zero on a nonempty open subregion of a preconnected domain is
zero on the whole domain. -/
theorem analytic_eq_zero_of_eq_zero_on_nonempty_open
    {U V : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hVne : V.Nonempty)
    (hzero : EqOn f 0 V) :
    EqOn f 0 U := by
  obtain ⟨z, hzV⟩ := hVne
  apply hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU (hVU hzV)
  filter_upwards [hV.mem_nhds hzV] with w hw
  exact hzero hw

/-- No analytic scalar can be zero on one nonempty open subregion and one on another nonempty
subregion of the same preconnected complex domain. -/
theorem no_analytic_open_cutoff
    {U V W : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hVne : V.Nonempty)
    (hzero : EqOn f 0 V) (hWU : W ⊆ U) (hWne : W.Nonempty)
    (hone : EqOn f 1 W) :
    False := by
  obtain ⟨w, hw⟩ := hWne
  have hglobal := analytic_eq_zero_of_eq_zero_on_nonempty_open hf hU hV hVU hVne hzero
  have hz : f w = 0 := hglobal (hWU hw)
  have ho : f w = 1 := hone hw
  exact zero_ne_one (hz.symm.trans ho)

end GaloisForLFunctions.HTGeometry
