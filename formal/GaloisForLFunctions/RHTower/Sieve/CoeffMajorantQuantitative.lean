import GaloisForLFunctions.RHTower.Sieve.CoeffRatioLimit

/-!
# The majorant against half the exponent

The contour argument's coefficient majorant is a polynomial in `t = (log x)^{1/10}`, and the
corpus's limit `coeffMajorant · exp(-κt) → 0` is used only qualitatively.  Splitting the exponential
turns it into a bound with an explicit rate:

    coeffMajorant C C' M₀ a t · exp(-κt) ≤ exp(-κt/2)   for all large `t`.

Half the exponent absorbs the whole polynomial.  This is what a short-interval application needs,
where a bare `o(1)` is not enough.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **Half the exponent absorbs the majorant.** -/
theorem eventually_coeffMajorant_mul_exp_le {C C' M₀ a κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ t : ℝ in atTop,
      coeffMajorant C C' M₀ a t * Real.exp (-(κ * t)) ≤ Real.exp (-(κ * t / 2)) := by
  have hhalf : (0 : ℝ) < κ / 2 := by linarith
  have h := tendsto_coeffMajorant_mul_exp_neg (C := C) (C' := C') (M₀ := M₀) (a := a) hhalf
  have h1 : ∀ᶠ t : ℝ in atTop,
      coeffMajorant C C' M₀ a t * Real.exp (-(κ / 2 * t)) ≤ 1 := by
    have hlt := h.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hlt] with t ht
    exact le_of_lt ht
  filter_upwards [h1] with t ht
  have hpos : (0 : ℝ) < Real.exp (-(κ * t / 2)) := Real.exp_pos _
  have hsplit : Real.exp (-(κ * t))
      = Real.exp (-(κ / 2 * t)) * Real.exp (-(κ * t / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, ← mul_assoc]
  calc coeffMajorant C C' M₀ a t * Real.exp (-(κ / 2 * t)) * Real.exp (-(κ * t / 2))
      ≤ 1 * Real.exp (-(κ * t / 2)) := mul_le_mul_of_nonneg_right ht hpos.le
    _ = Real.exp (-(κ * t / 2)) := one_mul _

end RHTower.Sieve
