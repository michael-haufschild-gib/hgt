import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Outer tails of an integrable energy density vanish

The integral of an integrable nonnegative density over the complement of a growing central
interval tends to zero.  This is the frequency-side tail estimate: once the carrier has pushed the
profile's spectrum past a growing radius, the energy left behind it is such a tail.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- The set of points beyond a given radius is measurable. -/
theorem measurableSet_outer (R : ℝ) : MeasurableSet {x : ℝ | R ≤ |x|} := by
  have : {x : ℝ | R ≤ |x|} = (fun x : ℝ => |x|) ⁻¹' (Set.Ici R) := rfl
  rw [this]
  exact (continuous_abs.measurable) measurableSet_Ici

/-- **Outer tails vanish.**  The mass of an integrable density beyond a growing radius tends to
zero. -/
theorem tendsto_integral_indicator_outer_atTop {g : ℝ → ℝ}
    (hnonneg : ∀ x, 0 ≤ g x) (hg : Integrable g volume)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, {x : ℝ | R n ≤ |x|}.indicator g x) atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable ({x : ℝ | R n ≤ |x|}.indicator g) volume :=
    fun n => hg.aestronglyMeasurable.indicator (measurableSet_outer (R n))
  have hbound : ∀ n : ℕ, ∀ᵐ x : ℝ, ‖{x : ℝ | R n ≤ |x|}.indicator g x‖ ≤ g x := by
    intro n
    filter_upwards with x
    by_cases hmem : x ∈ {x : ℝ | R n ≤ |x|}
    · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      exact hnonneg x
  have hlim : ∀ᵐ x : ℝ,
      Tendsto (fun n : ℕ => {x : ℝ | R n ≤ |x|}.indicator g x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with x
    have hev : ∀ᶠ n : ℕ in atTop, {x : ℝ | R n ≤ |x|}.indicator g x = 0 := by
      filter_upwards [hR.eventually_gt_atTop |x|] with n hn
      have hnot : x ∉ {y : ℝ | R n ≤ |y|} := by
        simp only [Set.mem_setOf_eq, not_le]
        exact hn
      exact Set.indicator_of_notMem hnot g
    exact Tendsto.congr' (by filter_upwards [hev] with n hn; rw [hn]) tendsto_const_nhds
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence g hmeas hg hbound hlim
  rw [integral_zero] at hdct
  exact hdct

end RHTower
