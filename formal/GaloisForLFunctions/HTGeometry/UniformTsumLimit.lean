import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

/-!
# Limits of uniformly convergent series

A normally convergent series of functions may be passed to the limit term by term along any
filter on which the domination holds.
-/

open Filter Topology

namespace HTGeometry

theorem tendsto_tsum_of_tendsto_of_norm_bounded_on
    {ι : Type*} {f : ι → ℝ → ℂ} {u : ι → ℝ} {s : Set ℝ} {l : Filter ℝ} [l.NeBot]
    (hls : s ∈ l) {L : ι → ℂ}
    (hu : Summable u) (hfu : ∀ i, ∀ x ∈ s, ‖f i x‖ ≤ u i)
    (hL : Summable L) (hlim : ∀ i, Tendsto (f i) l (𝓝 (L i))) :
    Tendsto (fun x => ∑' i, f i x) l (𝓝 (∑' i, L i)) := by
  have h1 := tendstoUniformlyOn_tsum (f := f) (s := s) hu (fun n x hx => hfu n x hx)
  have h2 : TendstoUniformlyOnFilter (fun t : Finset ι => fun x => ∑ i ∈ t, f i x)
      (fun x => ∑' i, f i x) atTop l :=
    h1.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr hls)
  refine h2.tendsto_of_eventually_tendsto ?_ hL.hasSum
  filter_upwards with t
  exact tendsto_finsetSum _ fun i _ => hlim i

end HTGeometry
