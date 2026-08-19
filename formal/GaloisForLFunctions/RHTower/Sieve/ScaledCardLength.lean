import GaloisForLFunctions.RHTower.Sieve.PolyDecayLimits

/-!
# The window length, scaled by a constant

The Route E marker construction uses cofactor windows of length `h/2^k` at starts `√x/2^k` for
`k = 0, …, K`: the cell of a marker at `2^k√x` is `H/p ≍ h/2^k`, so the fibre must shrink with the
marker scale while the physical cell `(X, X+H]` stays fixed.  The corpus's window function
`cardLength β` is nearly scale-invariant, so those windows are *not* `cardLength β` at any scale;
they are `c · cardLength β` with `c = 2^{-k}`.

Every asymptotic property of `cardLength β` that the spectral chain consumes is insensitive to a
positive constant factor, and this file transfers them.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The window length scaled by a positive constant. -/
def scaledLength (c β x : ℝ) : ℝ := c * cardLength β x

@[simp] theorem scaledLength_one (β x : ℝ) : scaledLength 1 β x = cardLength β x := by
  rw [scaledLength, one_mul]

theorem scaledLength_pos {c : ℝ} (hc : 0 < c) (β x : ℝ) : 0 < scaledLength c β x :=
  mul_pos hc (cardLength_pos β x)

theorem log_scaledLength {c : ℝ} (hc : 0 < c) (β x : ℝ) :
    Real.log (scaledLength c β x) = Real.log c + (Real.log x) ^ β := by
  rw [scaledLength, Real.log_mul (ne_of_gt hc) (ne_of_gt (cardLength_pos β x)), log_cardLength]

/-- **The scaled window grows.** -/
theorem tendsto_scaledLength {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    Tendsto (scaledLength c β) atTop atTop := by
  have h := (tendsto_cardLength hβ).const_mul_atTop hc
  exact h.congr fun x => rfl

/-- **The scaled window stays below `√x`** when the constant is at most one. -/
theorem scaledLength_le_sqrt {c β : ℝ} (hc1 : c ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, scaledLength c β x ≤ Real.sqrt x := by
  filter_upwards [cardLength_le_sqrt hβ0 hβ1] with x hx
  have h0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  calc scaledLength c β x = c * cardLength β x := rfl
    _ ≤ 1 * cardLength β x := mul_le_mul_of_nonneg_right hc1 h0.le
    _ = cardLength β x := one_mul _
    _ ≤ Real.sqrt x := hx

/-- A power of the logarithm is negligible against the scaled window. -/
theorem tendsto_rpow_log_div_scaledLength {c β : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (d : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ d / scaledLength c β x) atTop (𝓝 0) := by
  have hbase := tendsto_rpow_log_div_cardLength (β := β) hβ0 d
  have hmul := hbase.const_mul (1 / c)
  rw [mul_zero] at hmul
  refine hmul.congr fun x => ?_
  rw [scaledLength]
  field_simp

/-- The scaled window is negligible against the square root of the outer scale. -/
theorem tendsto_rpow_log_mul_scaledLength_div_sqrt {c β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (d : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ d * (scaledLength c β x / Real.sqrt x)) atTop (𝓝 0) := by
  have hbase := tendsto_rpow_log_mul_cardLength_div_sqrt (β := β) hβ0 hβ1 d
  have hmul := hbase.const_mul c
  rw [mul_zero] at hmul
  refine hmul.congr fun x => ?_
  rw [scaledLength]
  ring

end

end RHTower.Sieve
