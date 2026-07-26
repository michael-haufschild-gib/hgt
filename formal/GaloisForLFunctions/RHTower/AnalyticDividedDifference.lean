import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference

/-!
# Analyticity of removable divided differences

Minimal analytic lemma shared by Deninger's intrinsic Xi multiplicity chain and the carrier
estimates.  Keeping it here prevents source cohomology from importing the unrelated carrier
pipeline.
-/

open Complex

namespace RHTower

/-- The difference quotient `dslope f a` of an analytic function is analytic: at the base
point via the shifted power series, elsewhere as a quotient with nonvanishing denominator. -/
theorem analyticAt_dslope_of_analyticAt {f : ℂ → ℂ} {a z : ℂ}
    (ha : AnalyticAt ℂ f a) (hz : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (dslope f a) z := by
  rcases eq_or_ne z a with rfl | hne
  · obtain ⟨p, hp⟩ := ha
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  · have hq : AnalyticAt ℂ (fun w => (f w - f a) / (w - a)) z :=
      (hz.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hne)
    apply hq.congr
    filter_upwards [isOpen_ne.mem_nhds hne] with w hw
    rw [dslope_of_ne _ hw, slope_def_field]

end RHTower
