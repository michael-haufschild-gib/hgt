import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Two values at one point obstruct a continuous limit

A family that keeps attaining two separated values arbitrarily close to a point cannot have a
continuous limit there: the limit would have to equal both.  Two forms are proved.

The static form is about a single map: if both `a` and `b` are attained frequently near `y₀`, then
the map is not continuous at `y₀`.  The dynamic form is the one a normality argument uses: if
`Fₙ → G` uniformly on a set, `G` is continuous at `x`, and two sequences of points converge to `x`
along which `Fₙ` takes the constant values `a` and `b`, then `a = b`.

Neither form needs the maps to be analytic or the values to be finite: the target is any Hausdorff
(respectively, uniform Hausdorff) space, so `a = 0` and `b = ∞` on a compactified target are
admissible.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-! ## The static obstruction -/

/-- A value attained frequently near a point is the value at that point, if the map is continuous
there. -/
theorem eq_of_frequently_of_continuousAt {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    [T2Space X] {F : Y → X} {y₀ : Y} {a : X}
    (hcont : ContinuousAt F y₀) (hfreq : ∃ᶠ y in 𝓝 y₀, F y = a) : a = F y₀ := by
  by_contra hne
  obtain ⟨U, V, hU, hV, haU, hcV, hdisj⟩ := t2_separation hne
  have hev : ∀ᶠ y in 𝓝 y₀, F y ∈ V := hcont (hV.mem_nhds hcV)
  obtain ⟨y, hya, hyV⟩ := (hfreq.and_eventually hev).exists
  rw [hya] at hyV
  exact (Set.disjoint_left.mp hdisj haU) hyV

/-- **The static obstruction.**  Two separated values attained frequently near a point rule out
continuity there. -/
theorem not_continuousAt_of_frequently_two_values {Y X : Type*} [TopologicalSpace Y]
    [TopologicalSpace X] [T2Space X] {F : Y → X} {y₀ : Y} {a b : X} (hab : a ≠ b)
    (ha : ∃ᶠ y in 𝓝 y₀, F y = a) (hb : ∃ᶠ y in 𝓝 y₀, F y = b) :
    ¬ ContinuousAt F y₀ := by
  intro hcont
  exact hab ((eq_of_frequently_of_continuousAt hcont ha).trans
    (eq_of_frequently_of_continuousAt hcont hb).symm)

/-! ## The dynamic obstruction -/

/-- **The dynamic obstruction.**  Under uniform convergence to a limit continuous at `x`, two
sequences of points converging to `x` along which the family takes constant values force those
values to agree.  Contrapositively: interlacing level points converging to a common point rule out
a continuous uniform limit. -/
theorem eq_of_tendstoUniformlyOn_of_tendsto {ι : Type*} {Y X : Type*} [TopologicalSpace Y]
    [UniformSpace X] [T2Space X] {p : Filter ι} [p.NeBot]
    {F : ι → Y → X} {G : Y → X} {s : Set Y}
    (huc : TendstoUniformlyOn F G p s) {x : Y} (hG : ContinuousWithinAt G s x)
    {u v : ι → Y} (hu : Tendsto u p (𝓝[s] x)) (hv : Tendsto v p (𝓝[s] x))
    {a b : X} (hua : ∀ n, F n (u n) = a) (hvb : ∀ n, F n (v n) = b) : a = b := by
  have h1 : Tendsto (fun n => F n (u n)) p (𝓝 (G x)) := huc.tendsto_comp hG hu
  have h2 : Tendsto (fun n => F n (v n)) p (𝓝 (G x)) := huc.tendsto_comp hG hv
  have h1' : Tendsto (fun _ : ι => a) p (𝓝 (G x)) := by
    simpa [funext hua] using h1
  have h2' : Tendsto (fun _ : ι => b) p (𝓝 (G x)) := by
    simpa [funext hvb] using h2
  have ha : a = G x := tendsto_nhds_unique tendsto_const_nhds h1'
  have hb : b = G x := tendsto_nhds_unique tendsto_const_nhds h2'
  rw [ha, hb]

/-- **The normality obstruction.**  With two separated values there is no such limit. -/
theorem not_continuousWithinAt_of_tendstoUniformlyOn {ι : Type*} {Y X : Type*}
    [TopologicalSpace Y] [UniformSpace X] [T2Space X] {p : Filter ι} [p.NeBot]
    {F : ι → Y → X} {G : Y → X} {s : Set Y}
    (huc : TendstoUniformlyOn F G p s) {x : Y}
    {u v : ι → Y} (hu : Tendsto u p (𝓝[s] x)) (hv : Tendsto v p (𝓝[s] x))
    {a b : X} (hab : a ≠ b) (hua : ∀ n, F n (u n) = a) (hvb : ∀ n, F n (v n) = b) :
    ¬ ContinuousWithinAt G s x := fun hG =>
  hab (eq_of_tendstoUniformlyOn_of_tendsto huc hG hu hv hua hvb)

/-! ## Producing the converging sequences

A shrinking schedule of level points is exactly a sequence converging to the point.
-/

/-- Level points found in shrinking windows assemble into a sequence converging to the centre. -/
theorem exists_tendsto_of_forall_exists_close {x₀ : ℝ} {P : ℕ → ℝ → Prop}
    (h : ∀ n : ℕ, ∃ y : ℝ, |y - x₀| < 1 / ((n : ℝ) + 1) ∧ P n y) :
    ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝 x₀) ∧ ∀ n, P n (u n) := by
  choose u hu1 hu2 using h
  refine ⟨u, ?_, hu2⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Real.dist_eq]
  exact (hu1 n).le

/-- **The assembled normality obstruction.**  Two separated values attained on shrinking windows
about `x₀` rule out a continuous uniform limit there. -/
theorem not_continuousWithinAt_of_shrinking_levels {X : Type*} [UniformSpace X] [T2Space X]
    {F : ℕ → ℝ → X} {G : ℝ → X} {s : Set ℝ} (huc : TendstoUniformlyOn F G atTop s)
    {x₀ : ℝ} {a b : X} (hab : a ≠ b)
    (ha : ∀ n : ℕ, ∃ y : ℝ, |y - x₀| < 1 / ((n : ℝ) + 1) ∧ y ∈ s ∧ F n y = a)
    (hb : ∀ n : ℕ, ∃ y : ℝ, |y - x₀| < 1 / ((n : ℝ) + 1) ∧ y ∈ s ∧ F n y = b) :
    ¬ ContinuousWithinAt G s x₀ := by
  obtain ⟨u, hu, hua⟩ := exists_tendsto_of_forall_exists_close ha
  obtain ⟨v, hv, hvb⟩ := exists_tendsto_of_forall_exists_close hb
  refine not_continuousWithinAt_of_tendstoUniformlyOn huc ?_ ?_ hab
    (fun n => (hua n).2) (fun n => (hvb n).2)
  · exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu
      (Filter.Eventually.of_forall fun n => (hua n).1)
  · exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within v hv
      (Filter.Eventually.of_forall fun n => (hvb n).1)

end GaloisForLFunctions.HTGeometry
