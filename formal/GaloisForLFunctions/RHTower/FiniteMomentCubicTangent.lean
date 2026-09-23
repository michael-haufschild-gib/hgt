import GaloisForLFunctions.RHTower.FiniteTwoLevelMomentCarrier

/-!
# Cubic tangent law on a finite moment fiber

Move one distinguished atom `x`, `k` equal residual atoms `a`, and one
residual atom `b` while preserving the first two power sums to first order.
The cubic change factors exactly.  This is the local monotonicity mechanism
for sweeping from a padded reverse head toward a large-count upper head.
-/

namespace RHTower

noncomputable section

theorem fixedMoment_cubic_tangent_identity
    {k x a b u v w : ℝ}
    (hmass : u + k * v + w = 0)
    (henergy : x * u + k * a * v + b * w = 0) :
    x ^ (2 : ℕ) * u + k * a ^ (2 : ℕ) * v +
        b ^ (2 : ℕ) * w = (x - a) * (x - b) * u := by
  have hid :
      x ^ (2 : ℕ) * u + k * a ^ (2 : ℕ) * v +
          b ^ (2 : ℕ) * w - (x - a) * (x - b) * u =
        -(a * b) * (u + k * v + w) +
          (a + b) * (x * u + k * a * v + b * w) := by
    ring
  rw [hmass, henergy] at hid
  linarith

/-- Increasing a distinguished atom already larger than the residual pair
strictly increases the cubic power sum along any first/second-moment tangent. -/
theorem fixedMoment_cubic_tangent_pos
    {k x a b u v w : ℝ}
    (hmass : u + k * v + w = 0)
    (henergy : x * u + k * a * v + b * w = 0)
    (hba : b ≤ a) (hax : a < x) (hu : 0 < u) :
    0 < x ^ (2 : ℕ) * u + k * a ^ (2 : ℕ) * v +
      b ^ (2 : ℕ) * w := by
  rw [fixedMoment_cubic_tangent_identity hmass henergy]
  exact mul_pos
    (mul_pos (sub_pos.mpr hax) (sub_pos.mpr (lt_of_le_of_lt hba hax))) hu

end

end RHTower
