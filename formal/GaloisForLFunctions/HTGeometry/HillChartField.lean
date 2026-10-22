import GaloisForLFunctions.HTGeometry.HillRealField
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonConformalProbe

/-!
# The evolution field on the chart

The corpus's coordinate calculus reads a field as a function of an event `y : Fin (d+1) → ℝ`, whose
time is `y 0` and whose point is `kgSpatial d y`. This file transports the real field of the
time-dependent-speed evolution to that chart and records its nonvanishing near an event, which is the
first of the two facts a clock probe needs.

The transport is a composition with a continuous map, so nothing analytic happens here; the content
is that the neighbourhood produced in the product `ℝ × E` pulls back to a neighbourhood of the event.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section ChartField

variable {d : ℕ} {m K C cmin : ℝ} {c dc : ℝ → ℝ}
  {G₀ : EuclideanSpace ℝ (Fin d) → ℂ}

/-- The evolution field as a function of the event. -/
noncomputable def hillChartField (m : ℝ) (c : ℝ → ℝ) (G₀ : EuclideanSpace ℝ (Fin d) → ℂ)
    (y : Fin (d + 1) → ℝ) : ℝ :=
  hillRealField m c G₀ (y 0) (kgSpatial d y)

theorem hillChartField_apply (m : ℝ) (c : ℝ → ℝ) (G₀ : EuclideanSpace ℝ (Fin d) → ℂ)
    (y : Fin (d + 1) → ℝ) :
    hillChartField m c G₀ y = hillRealField m c G₀ (y 0) (kgSpatial d y) := rfl

/-- **The chart field does not vanish near an event on the initial slice** whose datum has a
nonvanishing real synthesis there. -/
theorem eventually_hillChartField_ne_zero (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    (hG : Continuous G₀)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G₀ ξ‖) (volume))
    {y₀ : Fin (d + 1) → ℝ} (hy₀ : y₀ 0 = 0)
    (hne : (kgSynthesis G₀ (kgSpatial d y₀)).re ≠ 0) :
    ∀ᶠ y in nhds y₀, hillChartField m c G₀ y ≠ 0 := by
  have hbase := eventually_hillRealField_ne_zero (m := m) (c := c) (G₀ := G₀) hm hc hcd hcpos hK hC
    hcmin hclow hG hint (x₀ := kgSpatial d y₀) hne
  have hcont : Continuous fun y : Fin (d + 1) → ℝ =>
      ((y 0, kgSpatial d y) : ℝ × EuclideanSpace ℝ (Fin d)) :=
    (continuous_apply 0).prodMk (kgSpatialCLM d).continuous
  have hmap : Filter.Tendsto (fun y : Fin (d + 1) → ℝ =>
      ((y 0, kgSpatial d y) : ℝ × EuclideanSpace ℝ (Fin d))) (nhds y₀)
      (nhds ((0 : ℝ), kgSpatial d y₀)) := by
    have h : Filter.Tendsto (fun y : Fin (d + 1) → ℝ =>
        ((y 0, kgSpatial d y) : ℝ × EuclideanSpace ℝ (Fin d))) (nhds y₀)
        (nhds ((y₀ 0, kgSpatial d y₀) : ℝ × EuclideanSpace ℝ (Fin d))) := hcont.continuousAt
    rwa [hy₀] at h
  exact hmap.eventually hbase

/-! ## Moving along a coordinate line -/

/-- Adding a multiple of a coordinate direction is updating that coordinate. -/
theorem add_smul_single_eq_update {n : ℕ} (y : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    y + s • Pi.single i (1 : ℝ) = Function.update y i (y i + s) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

/-- **Along the time axis the chart field moves only its time argument.** -/
theorem hillChartField_add_smul_single_zero (m : ℝ) (c : ℝ → ℝ)
    (G₀ : EuclideanSpace ℝ (Fin d) → ℂ) (y : Fin (d + 1) → ℝ) (s : ℝ) :
    hillChartField m c G₀ (y + s • Pi.single 0 (1 : ℝ))
      = hillRealField m c G₀ (y 0 + s) (kgSpatial d y) := by
  rw [add_smul_single_eq_update, hillChartField, kgSpatial_update_zero, Function.update_self]

/-- **Along a spatial axis the chart field moves its point along the rescaled direction.** -/
theorem hillChartField_add_smul_single_succ (m : ℝ) (c : ℝ → ℝ)
    (G₀ : EuclideanSpace ℝ (Fin d) → ℂ) (y : Fin (d + 1) → ℝ) (j : Fin d) (s : ℝ) :
    hillChartField m c G₀ (y + s • Pi.single j.succ (1 : ℝ))
      = hillRealField m c G₀ (y 0) (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d j)) := by
  rw [add_smul_single_eq_update, hillChartField, kgSpatial_update_succ]
  have htime : Function.update y j.succ (y j.succ + s) 0 = y 0 :=
    Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)) _ _
  rw [htime]
  have hscalar : y j.succ + s - y j.succ = s := by ring
  rw [hscalar]

end ChartField

end GaloisForLFunctions.HTGeometry
