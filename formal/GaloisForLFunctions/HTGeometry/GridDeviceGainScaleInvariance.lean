import GaloisForLFunctions.HTGeometry.GridDeviceCellEstimate

/-!
# The grid device's required gain is a shape quantity

On a window of length `T`, write `I₁ = ∫|f|` and `I₂ = ∫f²`.  Cauchy–Schwarz gives both
`I₁ ≤ √(T I₂)` and `Bsum ≤ √(T I₂)`, so the device closes only if the cell cancellation beats the
second bound by the factor `√(T I₂)/I₁`.

That factor is invariant under `f ↦ c f`.  A common amplitude in the mollified function — such as
the mean-square constant of the mollifier — therefore cancels between the two sides and cannot
contribute to the required gain.  The gain needed is a normalised `L¹/L²` shape ratio.
-/

namespace HTGeometry

/-- **The grid device's required gain is scale invariant.**  Writing `I₁ = ∫|f|` and `I₂ = ∫f²` on
a window of length `T`, the device must beat the Cauchy–Schwarz bound `Bsum ≤ √(T I₂)` by the
factor `√(T I₂)/I₁`.  Replacing `f` by `c f` sends `I₁ ↦ c I₁` and `I₂ ↦ c² I₂`, and leaves that
factor unchanged: the required gain is a **shape** quantity, not a scale one.

In particular a common amplitude factor in the mollified function — such as the mean-square
constant `λ` of the mollifier — cancels between the two sides and cannot contribute to the
required gain. -/
theorem grid_required_gain_scale_invariant {I1 I2 T c : ℝ} (hc : 0 < c) :
    (c * I1) / Real.sqrt (T * (c ^ 2 * I2)) = I1 / Real.sqrt (T * I2) := by
  have hrw : T * (c ^ 2 * I2) = c ^ 2 * (T * I2) := by ring
  rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (T * I2)) with h | h
  · rw [← h]
    simp
  · field_simp

end HTGeometry
