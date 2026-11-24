import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.DimOne
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Tactic

/-! # A transverse zero isolates a date on a quadratically flat contact set -/

open Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.ReturnLevels.AnalyticContacts
noncomputable section

private theorem flat_derivative {S : Set ℝ} {f : ℝ → ℝ} {K : ℝ} {x : ℝ}
    (h : ∀ y ∈ S, |f y-f x| ≤ K*|y-x|^2) : HasDerivWithinAt f 0 S x := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hlim : Tendsto (fun y : ℝ => K*|y-x|) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : ℝ => K*|y-x|) :=
      continuous_const.mul (continuous_id.sub continuous_const).abs
    simpa only [sub_self,abs_zero,mul_zero] using hc.continuousAt (x:=x)
  apply squeeze_zero_norm' _ (hlim.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hne : y≠x := hy.2
  rw [Real.norm_eq_abs,slope_def_field,abs_div]
  apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hne))).mpr
  simpa only [sq,mul_assoc] using h y hy.1

/-- A level graph with quadratic increments has horizontal tangent at
each accumulation point along the set. Its intersection with a zero
stratum transverse in time can therefore contain only isolated dates. -/
theorem countable_transverse {S : Set ℝ} {f : ℝ → ℝ} (K : ℝ)
    (hflat : ∀ x ∈ S, ∀ y ∈ S, |f y-f x| ≤ K*|y-x|^2)
    (Q : ℝ × ℝ → ℝ) (hQ : Differentiable ℝ Q)
    (hz : ∀ x ∈ S, Q (x,f x)=0)
    (ht : ∀ x ∈ S, fderiv ℝ Q (x,f x) (1,0) ≠ 0) : S.Countable := by
  letI : DiscreteTopology S := discreteTopology_of_noAccPts (by
    intro x hx hacc
    have h₀ := flat_derivative (hflat x hx)
    have hg := (hasDerivAt_id x).hasDerivWithinAt.prodMk h₀
    have h₁ := (hQ (x,f x)).hasFDerivAt.comp_hasDerivWithinAt x hg
    have h₂ : HasDerivWithinAt (fun y => Q (y,f y)) 0 S x :=
      (hasDerivWithinAt_const x S (0:ℝ)).congr_of_mem hz hx
    exact ht x hx ((h₁.derivWithin hacc.uniqueDiffWithinAt).symm.trans
      (h₂.derivWithin hacc.uniqueDiffWithinAt)))
  exact countable_coe_iff.mp inferInstance

#print axioms countable_transverse
end
end GaloisForLFunctions.HTGeometry.ReturnLevels.AnalyticContacts
