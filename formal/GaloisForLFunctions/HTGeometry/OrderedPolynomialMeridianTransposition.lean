import GaloisForLFunctions.HTGeometry.OrderedPolynomialBranchMultiplicity
import GaloisForLFunctions.HTGeometry.PolynomialFiberPowerCharts
import GaloisForLFunctions.HTGeometry.PolynomialChartCircleTransport
import Mathlib.GroupTheory.Perm.Support

open Polynomial Set Topology Metric Filter
open scoped unitInterval Classical
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- Every distinct actual critical value has a positive circle whose root monodromy is a
transposition. The circle, avoidance, and permutation are constructed from the polynomial. -/
theorem exists_positiveCircle_rootLoopTransport_isSwap {n : ℕ} (v : Parameter n)
    (hv : Function.Injective (valuesWithConstant v)) (j : Fin (n + 1)) :
    ∃ r : ℝ, 0 < r ∧ ∃ havoid : ∀ t k,
      positiveCirclePath (valuesWithConstant v j) (r ^ 2) t ≠ valuesWithConstant v k,
      (rootLoopTransport v (positiveCirclePath (valuesWithConstant v j) (r ^ 2))
        havoid).IsSwap := by
  let P := additivePolynomial v
  let c := valuesWithConstant v j
  have hP : P - C c ≠ 0 := (monic_fiberPolynomial v c).ne_zero
  obtain ⟨e, he, η, δ, hη, hδ, hinside, hcapture⟩ :=
    exists_polynomial_fiber_power_charts P c hP
  let a₀ : {a : ℂ // P.eval a = c} := ⟨position v j, by
    simp only [P, c, additivePolynomial, valuesWithConstant, eval_add, eval_C]⟩
  have hm₂ : (P - C c).rootMultiplicity (a₀ : ℂ) = 2 :=
    rootMultiplicity_fiberPolynomial_critical v (injective_position_of_injective_values v hv) j
  have hp₂ : ∀ z ∈ (e a₀).source, P.eval z = c + (e a₀ z) ^ 2 := by
    simpa only [hm₂] using (he a₀).2.2.2.2.2
  have hp₁ : ∀ a : {a : ℂ // P.eval a = c}, a ≠ a₀ →
      ∀ z ∈ (e a).source, P.eval z = c + e a z := by
    intro a ha
    have haroot : (fiberPolynomial v c).IsRoot (a : ℂ) := by
      simpa only [IsRoot, fiberPolynomial, eval_sub, eval_C, sub_eq_zero] using a.property
    have hane : (a : ℂ) ≠ position v j := fun h => ha (Subtype.ext h)
    have hm₁ : (P - C c).rootMultiplicity (a : ℂ) = 1 :=
      rootMultiplicity_fiberPolynomial_other v hv j haroot hane
    simpa only [hm₁, pow_one] using (he a).2.2.2.2.2
  have havnear : ∀ᶠ w in 𝓝 c, ∀ k : Fin (n + 1), k ≠ j → w ≠ valuesWithConstant v k := by
    apply eventually_all.mpr
    intro k
    by_cases hkj : k = j
    · exact Eventually.of_forall fun _ h => (h hkj).elim
    · have hck : c ≠ valuesWithConstant v k := fun h => hkj (hv h).symm
      have hn : {w : ℂ | w ≠ valuesWithConstant v k} ∈ 𝓝 c := isOpen_ne.mem_nhds hck
      filter_upwards [hn] with w hw using fun _ => hw
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp havnear
  have hbound : 0 < min η (min δ (min ε 1)) := by positivity
  obtain ⟨r, hr, hrbound⟩ := exists_between hbound
  rcases lt_min_iff.mp hrbound with ⟨hrη, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hrδ, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hrε, hrone⟩
  have hsq : r ^ 2 < r := by nlinarith
  have hsqη := hsq.trans hrη
  have hsqδ := hsq.trans hrδ
  have hsqε := hsq.trans hrε
  have hav : ∀ t k, positiveCirclePath c (r ^ 2) t ≠ valuesWithConstant v k := by
    intro t k
    by_cases hkj : k = j
    · subst k
      exact circleMap_ne_center (pow_ne_zero 2 hr.ne')
    · apply hεball _ k hkj
      simpa only [positiveCirclePath_apply, mem_ball, dist_eq_norm, circleMap_sub_center,
        norm_circleMap_zero, abs_of_nonneg (sq_nonneg r)] using hsqε
  have hquad : closedBall (0 : ℂ) r ⊆ (e a₀).target := by
    intro z hz
    apply hinside a₀
    exact lt_of_le_of_lt hz hrη
  obtain ⟨x, y, hxy, htx, hty, hclass⟩ :=
    quadratic_chart_circle_exchange v c (e a₀) r hr hquad hp₂ hav
  have hfixed : ∀ z : RootFiber v (c + (r ^ 2 : ℝ)), z ≠ x → z ≠ y →
      rootLoopTransport v (positiveCirclePath c (r ^ 2)) hav z = z := by
    intro z hzx hzy
    have hb : c + (r ^ 2 : ℝ) ∈ ball c δ := by
      simpa [mem_ball, dist_eq_norm, abs_of_nonneg (sq_nonneg r)] using hsqδ
    obtain ⟨a, hza⟩ := hcapture _ hb z z.property
    by_cases ha : a = a₀
    · subst a
      exact ((hclass z hza).elim hzx hzy).elim
    · apply linear_chart_circle_fixed v c (e a) (r ^ 2) (sq_nonneg r) _ (hp₁ a ha) hav z hza
      intro w hw
      apply hinside a
      exact lt_of_le_of_lt hw hsqη
  refine ⟨r, hr, hav, x, y, hxy, ?_⟩
  apply Equiv.ext
  intro z
  by_cases hzx : z = x
  · subst z
    simpa using htx
  by_cases hzy : z = y
  · subst z
    simpa using hty
  simpa [Equiv.swap_apply_def, hzx, hzy] using hfixed z hzx hzy

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
