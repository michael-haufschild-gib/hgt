import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Joint continuity from a uniform Lipschitz estimate

Separate continuity in each variable does not give joint continuity.  What does is continuity in one
variable together with a Lipschitz estimate in the other that is *uniform* over a neighbourhood of
the first.

That is exactly the situation for Cauchy-jet families: the parameter estimate is Lipschitz with a
constant built from the kernel bound, and that bound is uniform once the node stays away from the
real axis.  The triangle inequality then splits the increment into a Lipschitz part and a
one-variable continuity part.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Joint continuity from a locally uniform Lipschitz estimate.**  If the first variable moves the
value by at most `L` times its displacement, uniformly for the second variable near `y₀`, and the
value is continuous in the second variable at `y₀`, then the uncurried map is continuous at
`(x₀, y₀)`. -/
theorem continuousAt_uncurry_of_lipschitz_of_continuousAt
    {X Y E : Type*} [MetricSpace X] [TopologicalSpace Y] [NormedAddCommGroup E]
    (F : X → Y → E) {x₀ : X} {y₀ : Y} {L : ℝ} (hL : 0 ≤ L)
    {V : Set Y} (hV : V ∈ nhds y₀) {r : ℝ} (hr : 0 < r)
    (hlip : ∀ y ∈ V, ∀ x ∈ Metric.ball x₀ r, ‖F x y - F x₀ y‖ ≤ L * dist x x₀)
    (hcont : ContinuousAt (fun y => F x₀ y) y₀) :
    ContinuousAt (fun p : X × Y => F p.1 p.2) (x₀, y₀) := by
  rw [ContinuousAt, nhds_prod_eq, Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hW : {y | dist (F x₀ y) (F x₀ y₀) < ε / 2} ∈ nhds y₀ :=
    Metric.tendsto_nhds.mp hcont (ε / 2) hhalf
  have hδpos : 0 < ε / (2 * (L + 1)) := by positivity
  have hball : Metric.ball x₀ (min r (ε / (2 * (L + 1)))) ∈ nhds x₀ :=
    Metric.ball_mem_nhds x₀ (lt_min hr hδpos)
  filter_upwards [Filter.prod_mem_prod hball (Filter.inter_mem hV hW)] with p hp
  obtain ⟨hx, hyV, hyW⟩ := hp
  have hxmin : dist p.1 x₀ < min r (ε / (2 * (L + 1))) := Metric.mem_ball.mp hx
  have hxr : p.1 ∈ Metric.ball x₀ r :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hxmin (min_le_left _ _))
  have hxdist : dist p.1 x₀ < ε / (2 * (L + 1)) :=
    lt_of_lt_of_le hxmin (min_le_right _ _)
  have hlipp : ‖F p.1 p.2 - F x₀ p.2‖ ≤ L * dist p.1 x₀ := hlip p.2 hyV p.1 hxr
  have hcontp : dist (F x₀ p.2) (F x₀ y₀) < ε / 2 := hyW
  have hLbound : L * dist p.1 x₀ < ε / 2 := by
    have hLle : L * dist p.1 x₀ ≤ L * (ε / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left (le_of_lt hxdist) hL
    have hfrac : L * (ε / (2 * (L + 1))) < ε / 2 := by
      have h1 : L * (ε / (2 * (L + 1))) = (L / (L + 1)) * (ε / 2) := by
        field_simp
      have h2 : L / (L + 1) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      rw [h1]
      nlinarith
    exact lt_of_le_of_lt hLle hfrac
  calc dist (F p.1 p.2) (F x₀ y₀)
      ≤ dist (F p.1 p.2) (F x₀ p.2) + dist (F x₀ p.2) (F x₀ y₀) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add_of_le_of_lt _ hcontp
        rw [dist_eq_norm]
        exact le_of_lt (lt_of_le_of_lt hlipp hLbound)
    _ = ε := by ring

end

end GaloisForLFunctions.HTGeometry
