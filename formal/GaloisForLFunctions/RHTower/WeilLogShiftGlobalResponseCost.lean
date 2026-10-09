import GaloisForLFunctions.RHTower.WeilLogShiftExactResponseCost

/-!
# A single optimal observation point for every response and budget

A C₀ dual-valued family attains its global sensitivity at one point.
Finite-dimensional norm attainment then gives exact global response cost
at that same point, independently of the requested response and budget.
-/

open Filter Topology Real
open scoped ZeroAtInfty

noncomputable section

namespace RHTower

/-- Every C₀ map on a nonempty space attains its supremum norm. -/
theorem exists_c0_norm_attainer
    {X F : Type*} [TopologicalSpace X] [Nonempty X] [NormedAddCommGroup F]
    (f : C₀(X, F)) : ∃ x : X, ‖f x‖ = ‖f‖ := by
  classical
  by_cases hf : f = 0
  · obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨x, by simp [hf]⟩
  · have hex : ∃ x : X, f x ≠ 0 := by
      by_contra h
      push Not at h
      apply hf
      apply ZeroAtInftyContinuousMap.ext
      intro x
      exact h x
    obtain ⟨x₀, hx₀⟩ := hex
    have ht : Tendsto (fun x => ‖f x‖) (cocompact X) (𝓝 0) := by
      simpa only [norm_zero] using (zero_at_infty f).norm
    obtain ⟨x, hmax⟩ := (map_continuous f).norm.exists_forall_ge' x₀ (by
      filter_upwards [(tendsto_order.mp ht).2 ‖f x₀‖ (norm_pos_iff.mpr hx₀)] with y hy
      exact hy.le)
    refine ⟨x, le_antisymm ?_ ?_⟩
    · simpa only using! BoundedContinuousFunction.norm_coe_le_norm f.toBCF x
    · change ‖f.toBCF‖ ≤ ‖f x‖
      apply (BoundedContinuousFunction.norm_le (norm_nonneg (f x))).mpr
      intro y
      exact hmax y

/-- One observation point realizes every globally feasible response at its
minimum amplitude norm, for every target and every budget simultaneously. -/
theorem exists_c0_dual_optimal_response_point
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [Nonempty X] (Φ : C₀(X, E →L[ℝ] ℝ)) :
    ∃ x : X, ‖Φ x‖ = ‖Φ‖ ∧
      (∀ r A : ℝ, (∃ (y : X) (a : E), Φ y a = r ∧ ‖a‖ ≤ A) ↔
        0 ≤ A ∧ |r| ≤ A * ‖Φ‖) ∧
      ∀ r : ℝ, (∃ a : E, Φ x a = r ∧ ‖a‖ = |r| / ‖Φ‖ ∧
        ∀ (y : X) (b : E), Φ y b = r → ‖a‖ ≤ ‖b‖) ↔ r = 0 ∨ 0 < ‖Φ‖ := by
  obtain ⟨x, hx⟩ := exists_c0_norm_attainer Φ
  have hnorm (y : X) : ‖Φ y‖ ≤ ‖Φ‖ := by
    simpa only using! BoundedContinuousFunction.norm_coe_le_norm Φ.toBCF y
  have hbudget (r A : ℝ) : (∃ (y : X) (a : E), Φ y a = r ∧ ‖a‖ ≤ A) ↔
      0 ≤ A ∧ |r| ≤ A * ‖Φ‖ := by
    constructor
    · rintro ⟨y, a, ha, hA⟩
      obtain ⟨hA0, hr⟩ := (finiteDimensional_dual_response_budget_iff (Φ y) r A).mp ⟨a, ha, hA⟩
      exact ⟨hA0, hr.trans (mul_le_mul_of_nonneg_left (hnorm y) hA0)⟩
    · intro h
      have hlocal : ∃ a : E, Φ x a = r ∧ ‖a‖ ≤ A := by
        apply (finiteDimensional_dual_response_budget_iff (Φ x) r A).mpr
        simpa only [hx] using h
      obtain ⟨a, ha, hA⟩ := hlocal
      exact ⟨x, a, ha, hA⟩
  refine ⟨x, hx, hbudget, ?_⟩
  intro r
  constructor
  · rintro ⟨a, ha, hn, hmin⟩
    have hlocal : ∃ a : E, Φ x a = r ∧ ‖a‖ = |r| / ‖Φ x‖ ∧
        ∀ b : E, Φ x b = r → ‖a‖ ≤ ‖b‖ :=
      ⟨a, ha, by simpa only [hx] using hn, fun b hb => hmin x b hb⟩
    simpa only [hx] using (finiteDimensional_dual_minimum_response_iff (Φ x) r).mp hlocal
  · intro hr
    have hr' : r = 0 ∨ 0 < ‖Φ x‖ := by simpa only [hx] using hr
    obtain ⟨a, ha, hn, _⟩ := (finiteDimensional_dual_minimum_response_iff (Φ x) r).mpr hr'
    have hn' : ‖a‖ = |r| / ‖Φ‖ := by simpa only [hx] using hn
    refine ⟨a, ha, hn', ?_⟩
    intro y b hb
    rw [hn']
    rcases hr with rfl | hQ
    · simpa only [abs_zero, zero_div] using norm_nonneg b
    · exact (div_le_iff₀ hQ).mpr ((hbudget r ‖b‖).mp ⟨y, b, hb, le_rfl⟩).2

end RHTower
