import Mathlib

/-!
# A continuous function nonzero at a point has positive square mass

If a continuous function is nonzero somewhere strictly inside an interval, its square has positive
integral over that interval: continuity keeps the square above a positive constant on a
subinterval, and the rest of the integrand is nonnegative.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Positive square mass.** -/
theorem integral_sq_pos_of_ne_zero {f : ℝ → ℝ} (hf : Continuous f) {a b x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo a b) (hne : f x₀ ≠ 0) : 0 < ∫ x in a..b, f x ^ (2 : ℕ) := by
  have hab : a < b := lt_trans hx₀.1 hx₀.2
  have hcont : Continuous fun x : ℝ => f x ^ (2 : ℕ) := hf.pow 2
  have hnn : ∀ x : ℝ, 0 ≤ f x ^ (2 : ℕ) := fun x => sq_nonneg _
  have hpos0 : 0 < f x₀ ^ (2 : ℕ) := by positivity
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ x, |x - x₀| < δ → f x₀ ^ (2 : ℕ) / 2 < f x ^ (2 : ℕ) := by
    have hc := hcont.continuousAt (x := x₀)
    have hev := hc.eventually (eventually_gt_nhds (by linarith : f x₀ ^ (2 : ℕ) / 2 < f x₀ ^ (2 : ℕ)))
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, h⟩ := hev
    exact ⟨δ, hδ, fun x hx => h (by rwa [Real.dist_eq])⟩
  set α : ℝ := max a (x₀ - δ / 2) with hα
  set β : ℝ := min b (x₀ + δ / 2) with hβ
  have hαx : α < x₀ := max_lt hx₀.1 (by linarith)
  have hxβ : x₀ < β := lt_min hx₀.2 (by linarith)
  have hαβ : α < β := lt_trans hαx hxβ
  have haα : a ≤ α := le_max_left _ _
  have hβb : β ≤ b := min_le_left _ _
  have hmid : 0 < ∫ x in α..β, f x ^ (2 : ℕ) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable α β) (fun x hx => ?_) hαβ
    refine lt_trans (by linarith) (hball x ?_)
    rw [abs_lt]
    constructor
    · have h1 : x₀ - δ / 2 ≤ α := le_max_right _ _
      have h2 := hx.1
      linarith
    · have h1 : β ≤ x₀ + δ / 2 := min_le_right _ _
      have h2 := hx.2
      linarith
  have hsplit1 : (∫ x in a..α, f x ^ (2 : ℕ)) + ∫ x in α..β, f x ^ (2 : ℕ) = ∫ x in a..β, f x ^ (2 : ℕ) :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hsplit2 : (∫ x in a..β, f x ^ (2 : ℕ)) + ∫ x in β..b, f x ^ (2 : ℕ) = ∫ x in a..b, f x ^ (2 : ℕ) :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hleft : (0 : ℝ) ≤ ∫ x in a..α, f x ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg haα (fun x _ => hnn x)
  have hright : (0 : ℝ) ≤ ∫ x in β..b, f x ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg hβb (fun x _ => hnn x)
  linarith [hsplit1, hsplit2, hmid, hleft, hright]

end GaloisForLFunctions.HTGeometry
