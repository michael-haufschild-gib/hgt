import GaloisForLFunctions.HTGeometry.NevZeroDichotomy

/-!
# A tunable square inequality

The transfer estimate of `ComplexSecondKind` bounds `(a + b)²` by `2a² + 2b²`, which forces the
propagated kernel bound to double at every step: the leading constant is `2` no matter how small the
displacement is.  Young's inequality gives `(a + b)² ≤ (1 + ε)a² + (1 + ε⁻¹)b²` for any `ε > 0`,
so the leading constant can be taken as close to `1` as desired, at the cost of a larger coefficient
on the second term.

This is the ingredient a non-doubling transfer needs.
-/

open scoped BigOperators

namespace HTGeometry

/-- **Young's inequality in squared form.**  The leading constant is tunable, and no sign
hypothesis on `a` or `b` is needed. -/
theorem sq_add_le_tunable {a b e : ℝ} (he : 0 < e) :
    (a + b) ^ (2 : ℕ) ≤ (1 + e) * a ^ (2 : ℕ) + (1 + e⁻¹) * b ^ (2 : ℕ) := by
  have key : 2 * a * b ≤ e * a ^ (2 : ℕ) + e⁻¹ * b ^ (2 : ℕ) := by
    rw [← sub_nonneg]
    have hid : e * a ^ (2 : ℕ) + e⁻¹ * b ^ (2 : ℕ) - 2 * a * b = e⁻¹ * (e * a - b) ^ (2 : ℕ) := by
      field_simp
      ring
    rw [hid]
    positivity
  nlinarith [key]

/-- The classical constant is the case `ε = 1`. -/
theorem sq_add_le_two (a b : ℝ) : (a + b) ^ (2 : ℕ) ≤ 2 * a ^ (2 : ℕ) + 2 * b ^ (2 : ℕ) := by
  have h := sq_add_le_tunable (a := a) (b := b) (by norm_num : (0:ℝ) < 1)
  norm_num at h
  linarith

end HTGeometry
