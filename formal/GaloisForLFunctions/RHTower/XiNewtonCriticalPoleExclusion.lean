import GaloisForLFunctions.RHTower.XiNewtonDiscSourceMargin
import GaloisForLFunctions.RHTower.XiDerivReflection
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# Closed-disc source margins and the central Xi Newton pole

Continuity extends a nonnegative Newton source margin from an open disc to its
closure. A nonroot critical point has strictly negative margin, so even a boundary
critical point obstructs disc invariance.

At the center `1/2`, Xi is nonzero and its derivative vanishes. The totalized Newton
formula fixes that point, but it is not locally bounded or holomorphic there. No
positive-radius invariant disc can contain that point in its closure.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace RHTower.XiNewtonCriticalLine

/-- The closed-disc formulation is exact for every positive radius. -/
theorem xi_newton_closed_margin_iff (c : ℂ) (r : ℝ) :
    (0 < r ∧ MapsTo (newtonMap xi) (ball c r) (closedBall c r)) ↔
      (0 < r ∧ ∀ z ∈ closedBall c r, 0 ≤ xiNewtonDiscMargin c r z) := by
  constructor
  · rintro ⟨hr, hmap⟩
    refine ⟨hr, ?_⟩
    have hinterior := (xi_newton_mapsTo_closedBall_iff_source_margin c r).mp hmap
    have hclosed : IsClosed {z | 0 ≤ xiNewtonDiscMargin c r z} :=
      isClosed_le continuous_const (continuous_xiNewtonDiscMargin c r)
    have hclosure := closure_minimal hinterior hclosed
    rwa [closure_ball c hr.ne'] at hclosure
  · rintro ⟨hr, hmargin⟩
    exact ⟨hr, (xi_newton_mapsTo_closedBall_iff_source_margin c r).mpr
      (fun z hz => hmargin z (ball_subset_closedBall hz))⟩

/-- Every nonroot critical point lies strictly beyond a certified closed-disc radius. -/
theorem xi_newton_margin_critical_exclusion (c : ℂ) (r : ℝ) :
    (∀ z ∈ closedBall c r, 0 ≤ xiNewtonDiscMargin c r z) →
      ∀ p : ℂ, deriv xi p = 0 → xi p ≠ 0 → r < dist p c := by
  intro hmargin p hp hxi
  by_contra hdist
  have hmem : p ∈ closedBall c r := mem_closedBall.mpr (le_of_not_gt hdist)
  have hnonneg := hmargin p hmem
  simp only [xiNewtonDiscMargin, hp, normSq_zero, mul_zero, zero_sub,
    normSq_neg] at hnonneg
  have hpos := normSq_pos.mpr hxi
  linarith

/-- The central Xi Newton source margin is strictly negative at every radius. -/
theorem xiNewtonDiscMargin_half_neg (c : ℂ) (r : ℝ) :
    xiNewtonDiscMargin c r (1 / 2) < 0 := by
  have hxi : xi (1 / 2 : ℂ) ≠ 0 := by
    simpa using xi_ne_zero_of_real (1 / 2)
  simp only [xiNewtonDiscMargin, deriv_xi_half, normSq_zero, mul_zero, zero_sub,
    normSq_neg]
  exact neg_neg_of_pos (normSq_pos.mpr hxi)

/-- The center is a spurious fixed point of the totalized formula and a genuine analytic pole. -/
theorem xi_newton_half_fixed_but_not_locally_bounded :
    newtonMap xi (1 / 2) = 1 / 2 ∧ ¬ XiNewtonLocallyBounded (1 / 2) := by
  constructor
  · rw [newtonMap, deriv_xi_half, div_zero, sub_zero]
  · rw [xiNewtonLocallyBounded_iff]
    have hxi : xi (1 / 2 : ℂ) ≠ 0 := by
      simpa using xi_ne_zero_of_real (1 / 2)
    rintro (hzero | hderiv)
    · exact hxi hzero
    · exact hderiv deriv_xi_half

/-- No Xi Newton invariant disc can contain the central pole even on its boundary. -/
theorem not_exists_xi_newton_invariant_disc_containing_half :
    ¬ ∃ c : ℂ, ∃ r > 0, (1 / 2 : ℂ) ∈ closedBall c r ∧
      MapsTo (newtonMap xi) (ball c r) (ball c r) := by
  rintro ⟨c, r, hr, hhalf, hmap⟩
  have hmargin := ((xi_newton_closed_margin_iff c r).mp
    ⟨hr, hmap.mono_right ball_subset_closedBall⟩).2
  exact (not_le.mpr (xiNewtonDiscMargin_half_neg c r)) (hmargin _ hhalf)

/-- RH is exactly coverage by line-centered discs with nonnegative closed-disc source margin. -/
theorem riemannHypothesis_iff_xi_newton_closed_margin :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 →
      ∃ c : ℂ, c.re = 1 / 2 ∧ ∃ r > 0, ρ ∈ ball c r ∧
        ∀ z ∈ closedBall c r, 0 ≤ xiNewtonDiscMargin c r z := by
  rw [riemannHypothesis_iff_xi_newton_nonnegative_margin]
  constructor
  · intro h ρ hzero
    obtain ⟨c, hc, r, hr, hρ, hmargin⟩ := h ρ hzero
    have hmap := (xi_newton_mapsTo_closedBall_iff_source_margin c r).mpr hmargin
    exact ⟨c, hc, r, hr, hρ, ((xi_newton_closed_margin_iff c r).mp ⟨hr, hmap⟩).2⟩
  · intro h ρ hzero
    obtain ⟨c, hc, r, hr, hρ, hmargin⟩ := h ρ hzero
    exact ⟨c, hc, r, hr, hρ, fun z hz => hmargin z (ball_subset_closedBall hz)⟩

end RHTower.XiNewtonCriticalLine
