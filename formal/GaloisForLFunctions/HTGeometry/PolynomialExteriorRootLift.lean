import GaloisForLFunctions.HTGeometry.PolynomialExteriorPowerChart
import GaloisForLFunctions.HTGeometry.PolynomialRootLoopTransport
import GaloisForLFunctions.HTGeometry.PowerRootCirclePaths

open Polynomial Filter Topology Set Metric
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- An explicit lift of the positive exterior circle, with its infinity coordinate at every time. -/
theorem PolynomialExteriorPowerChart.exists_root_lift {n : ℕ} {v : Parameter n}
    (D : PolynomialExteriorPowerChart v)
    (z : RootFiber v (0 + ((D.radius ^ (n + 2))⁻¹ : ℝ))) :
    ∃ u : C(I, ℂ), u 0 = z ∧
      (∀ t, (additivePolynomial v).eval (u t) =
        positiveCirclePath 0 (D.radius ^ (n + 2))⁻¹ t) ∧
      ∀ t, D.chart (u t)⁻¹ = D.chart (z : ℂ)⁻¹ * (powerRootCirclePhase (n + 2) t)⁻¹ := by
  let R := (D.radius ^ (n + 2))⁻¹
  let c := D.chart (z : ℂ)⁻¹
  have hz : (additivePolynomial v).eval (z : ℂ) = positiveCirclePath 0 R 0 :=
    z.property.trans (positiveCirclePath 0 R).source.symm
  have hnorm : ‖c‖ = D.radius := D.norm_coordinate hz
  have hc0 : c ≠ 0 := D.coordinate_ne_zero hz
  have hzs := D.roots_outside 0 z hz
  have hcpow : c ^ (n + 2) = (R : ℂ)⁻¹ := by
    have h := D.reciprocal_power (z : ℂ)⁻¹ hzs.2 (inv_ne_zero hzs.1)
    simpa only [inv_inv, z.property, zero_add] using h
  let a : C(I, ℂ) := ⟨fun t => c * (powerRootCirclePhase (n + 2) t)⁻¹,
    continuous_const.mul ((powerRootCirclePhase (n + 2)).continuous.inv₀
      (powerRootCirclePhase_ne_zero (n + 2)))⟩
  have ha : ∀ t, a t ∈ D.chart.target := by
    intro t
    apply D.target_disk
    change dist (c * (powerRootCirclePhase (n + 2) t)⁻¹) 0 ≤ D.radius
    simp only [dist_zero_right, norm_mul, norm_inv, norm_powerRootCirclePhase,
      inv_one, mul_one, hnorm, le_refl]
  have ha0 : ∀ t, a t ≠ 0 := by
    intro t
    exact mul_ne_zero hc0 (inv_ne_zero (powerRootCirclePhase_ne_zero _ t))
  let w : C(I, ℂ) := ⟨fun t => D.chart.symm (a t),
    D.chart.continuousOn_symm.comp_continuous a.continuous ha⟩
  have hws : ∀ t, w t ∈ D.chart.source := fun t => D.chart.map_target (ha t)
  have hwcoord : ∀ t, D.chart (w t) = a t := fun t => D.chart.right_inv (ha t)
  have hw0 : ∀ t, w t ≠ 0 := by
    intro t h
    have he := hwcoord t
    rw [h, D.chart_zero] at he
    exact ha0 t he.symm
  let u : C(I, ℂ) := ⟨fun t => (w t)⁻¹, w.continuous.inv₀ hw0⟩
  refine ⟨u, ?_, ?_, ?_⟩
  · change (D.chart.symm (c * (powerRootCirclePhase (n + 2) 0)⁻¹))⁻¹ = z
    rw [powerRootCirclePhase_zero, inv_one, mul_one]
    change (D.chart.symm (D.chart (z : ℂ)⁻¹))⁻¹ = z
    rw [D.chart.left_inv hzs.2, inv_inv]
  · intro t
    apply inv_injective
    have hp := D.reciprocal_power (w t) (hws t) (hw0 t)
    change D.chart (w t) ^ (n + 2) = ((additivePolynomial v).eval (u t))⁻¹ at hp
    rw [hwcoord t] at hp
    refine hp.symm.trans ?_
    change (c * (powerRootCirclePhase (n + 2) t)⁻¹) ^ (n + 2) =
      (positiveCirclePath 0 R t)⁻¹
    rw [mul_pow, inv_pow, hcpow, powerRootCirclePhase_pow (n + 2) (by omega)]
    change (R : ℂ)⁻¹ * (circleMap 0 1 (2 * Real.pi * (t : ℝ)))⁻¹ =
      (circleMap 0 R (2 * Real.pi * (t : ℝ)))⁻¹
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, mul_inv_rev, mul_comm]
  · intro t
    change D.chart ((w t)⁻¹)⁻¹ = a t
    rw [inv_inv, hwcoord t]

/-- The actual positive-circle root permutation rotates the infinity coordinate negatively. -/
theorem PolynomialExteriorPowerChart.rootLoop_coordinate {n : ℕ} {v : Parameter n}
    (D : PolynomialExteriorPowerChart v)
    (z : RootFiber v (0 + ((D.radius ^ (n + 2))⁻¹ : ℝ))) :
    D.chart (rootLoopTransport v (positiveCirclePath 0 (D.radius ^ (n + 2))⁻¹)
      D.circle_avoid z : ℂ)⁻¹ =
      (Complex.exp (2 * Real.pi * Complex.I / ((n + 2 : ℕ) : ℂ)))⁻¹ *
        D.chart (z : ℂ)⁻¹ := by
  obtain ⟨u, hu0, hu, huc⟩ := D.exists_root_lift z
  have he := rootLoopTransport_val_eq_of_section v
    (positiveCirclePath 0 (D.radius ^ (n + 2))⁻¹) D.circle_avoid z u hu0 hu
  rw [he, huc 1, powerRootCirclePhase_one]
  exact mul_comm _ _

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
