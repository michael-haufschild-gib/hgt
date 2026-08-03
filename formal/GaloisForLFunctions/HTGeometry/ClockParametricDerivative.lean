import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import GaloisForLFunctions.HTGeometry.ClockBivariateChart

/-!
# Differentiation under the integral sign for continuous data

The chart d'Alembertian reads the second partial derivatives of a field one direction at a time, so
applying it to the Goursat solution needs the *pure* second derivatives `∂ξ²u` and `∂η²u`, not only
the mixed ones. Those come from differentiating

`∂ξ u(ξ,η) = ∫_b^η K(ξ,t) u(ξ,t) dt`

again in `ξ`, that is, under the integral sign.

This file supplies the Leibniz rule in the form the bootstrap needs: for an integrand which is
jointly continuous and has a jointly continuous partial derivative in the parameter, the parametric
interval integral is differentiable and its derivative is the integral of the derivative. mathlib's
general statement carries measurability and domination hypotheses; for continuous data on a compact
rectangle they are all automatic.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory Metric

/-- **Leibniz rule for a parametric interval integral of continuous data.** -/
theorem hasDerivAt_parametric_intervalIntegral {f f' : ℝ → ℝ → ℝ}
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (hf' : Continuous fun p : ℝ × ℝ => f' p.1 p.2)
    (hderiv : ∀ z t : ℝ, HasDerivAt (fun w => f w t) (f' z t) z)
    (a b x : ℝ) :
    HasDerivAt (fun z => ∫ t in a..b, f z t) (∫ t in a..b, f' x t) x := by
  classical
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod
    (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hf'.continuousOn
  have hslice : ∀ z : ℝ, Continuous fun t => f z t :=
    fun z => hf.comp (continuous_const.prodMk continuous_id)
  have hslice' : ∀ z : ℝ, Continuous fun t => f' z t :=
    fun z => hf'.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.closedBall x 1) (bound := fun _ => C) (F := f) (F' := f')
    (closedBall_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun z => (hslice z).aestronglyMeasurable
  · exact (hslice x).intervalIntegrable a b
  · exact (hslice' x).aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro t ht z hz
    exact hC (z, t) ⟨hz, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ z _ => hderiv z t

/-- **Leibniz rule with the derivative hypothesis only near the point.** The bootstrap needs this
form, because the `ξ`-derivative of the Goursat solution is known only on the interval where the
characteristic equation holds. -/
theorem hasDerivAt_parametric_intervalIntegral_on {f f' : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) {x : ℝ} (hx : x ∈ s)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (hf' : Continuous fun p : ℝ × ℝ => f' p.1 p.2) (a b : ℝ)
    (hderiv : ∀ z ∈ s, ∀ t ∈ uIoc a b, HasDerivAt (fun w => f w t) (f' z t) z) :
    HasDerivAt (fun z => ∫ t in a..b, f z t) (∫ t in a..b, f' x t) x := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hs x hx
  have hsub : Metric.closedBall x (r / 2) ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x (r / 2)).prod
    (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hf'.continuousOn
  have hslice : ∀ z : ℝ, Continuous fun t => f z t :=
    fun z => hf.comp (continuous_const.prodMk continuous_id)
  have hslice' : ∀ z : ℝ, Continuous fun t => f' z t :=
    fun z => hf'.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.closedBall x (r / 2)) (bound := fun _ => C) (F := f) (F' := f')
    (closedBall_mem_nhds x (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun z => (hslice z).aestronglyMeasurable
  · exact (hslice x).intervalIntegrable a b
  · exact (hslice' x).aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro t ht z hz
    exact hC (z, t) ⟨hz, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht z hz => hderiv z (hsub hz) t ht

end GaloisForLFunctions.HTGeometry
