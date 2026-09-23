import GaloisForLFunctions.RHTower.SuzukiCoalescingHalfPlaneNormality

/-!
# Reflection and the quadratic factor for the coalescing resolvent

A meromorphic inner carrier satisfies `Θ(z̄)·conj Θ(z) = 1`, and the singularly normalized resolvent
is odd under conjugation-reflection.  Hence local boundedness on the upper half-plane transports to
the lower half-plane, and the deterministic quadratic factor `z²` is harmless on compact sets.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower

/-- **`(32)`: the coalescing resolvent is odd under conjugation-reflection.**  This is exactly the
meromorphic-inner reflection law, so upper-half-plane bounds transport downward. -/
theorem suzukiCoalescingResolvent_reflection {θ : ℂ → ℂ} {c : ℝ} {z : ℂ}
    (hθ : θ ((starRingEnd ℂ) z) * (starRingEnd ℂ) (θ z) = 1)
    (hne : 1 + θ z ≠ 0) :
    (starRingEnd ℂ) (suzukiCoalescingResolvent θ c ((starRingEnd ℂ) z))
      = -suzukiCoalescingResolvent θ c z := by
  have hwne : θ z ≠ 0 := by
    intro h
    rw [h, map_zero, mul_zero] at hθ
    exact zero_ne_one hθ
  have hconjne : (starRingEnd ℂ) (θ z) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hθ
    exact zero_ne_one hθ
  have hrefl : θ ((starRingEnd ℂ) z) = 1 / (starRingEnd ℂ) (θ z) := by
    field_simp
    linear_combination hθ
  have hconjrefl : (starRingEnd ℂ) (θ ((starRingEnd ℂ) z)) = 1 / θ z := by
    rw [hrefl, map_div₀, map_one, RingHomCompTriple.comp_apply, RingHom.id_apply]
  have hcconj : (starRingEnd ℂ) ((c : ℂ)) = (c : ℂ) := Complex.conj_ofReal c
  rw [suzukiCoalescingResolvent, suzukiCoalescingResolvent, map_div₀, map_sub, map_one,
    map_mul, hcconj, map_add, map_one, hconjrefl]
  rcases eq_or_ne (c : ℂ) 0 with hc | hc
  · rw [hc]
    simp
  · have hne' : θ z + 1 ≠ 0 := by rwa [add_comm] at hne
    field_simp [hne, hwne, hc]
    ring

/-- The deterministic quadratic factor is harmless on a compact set. -/
theorem norm_sq_mul_suzukiCoalescingResolvent_le {θ : ℂ → ℂ} {c A r : ℝ} {q z : ℂ}
    (hz : z ∈ Metric.closedBall q r)
    (hbd : ‖suzukiCoalescingResolvent θ c z‖ ≤ A) :
    ‖z ^ (2 : ℕ) * suzukiCoalescingResolvent θ c z‖ ≤ (‖q‖ + |r|) ^ (2 : ℕ) * A := by
  have hzq : ‖z - q‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hznorm : ‖z‖ ≤ ‖q‖ + |r| := by
    have h1 : ‖z‖ ≤ ‖z - q‖ + ‖q‖ := by
      calc ‖z‖ = ‖(z - q) + q‖ := by ring_nf
        _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
    have h2 : ‖z - q‖ ≤ |r| := le_trans hzq (le_abs_self r)
    linarith
  rw [norm_mul, norm_pow]
  refine mul_le_mul ?_ hbd (norm_nonneg _) (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg z) hznorm 2

end RHTower
