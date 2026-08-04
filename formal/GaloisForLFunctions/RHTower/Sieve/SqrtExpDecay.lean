import GaloisForLFunctions.RHTower.Sieve.PolyExpDecay

/-!
# A square-root exponential against a linear one

The smoothing width contributes a factor `exp(2√t)` where `t = (log x)^{1/10}`, because the width is
`x/exp((log x)^{1/20})` and `(log x)^{1/20} = √t`.  Every decaying factor in the contour bound is
`exp(-κt)` with `κ > 0`, and

    2√t - κt ≤ -κt/2   for   t ≥ (4/κ)²,

so the square-root growth is absorbed with half the exponent to spare.  The polynomial factors are
then handled by the polynomial-against-exponential estimate.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **A polynomial and a square-root exponential against a decaying exponential.** -/
theorem tendsto_poly_sqrt_exp_neg (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ => t ^ n * Real.exp (2 * Real.sqrt t) * Real.exp (-(κ * t)))
      atTop (𝓝 0) := by
  have hhalf : (0 : ℝ) < κ / 2 := by linarith
  have hmaj := tendsto_pow_mul_exp_neg_mul n hhalf
  have hnonneg : ∀ᶠ t : ℝ in atTop,
      0 ≤ t ^ n * Real.exp (2 * Real.sqrt t) * Real.exp (-(κ * t)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  have hle : ∀ᶠ t : ℝ in atTop,
      t ^ n * Real.exp (2 * Real.sqrt t) * Real.exp (-(κ * t))
        ≤ t ^ n * Real.exp (-(κ / 2 * t)) := by
    filter_upwards [eventually_ge_atTop ((4 / κ) ^ 2), eventually_ge_atTop (0 : ℝ)] with t ht ht0
    have hsqrt : 2 * Real.sqrt t ≤ κ / 2 * t := by
      have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
      have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
      have hge : 4 / κ ≤ Real.sqrt t := by
        have h1 : ((4 : ℝ) / κ) ^ 2 ≤ Real.sqrt t ^ 2 := by rw [hsq]; exact ht
        have h2 : (0 : ℝ) ≤ 4 / κ := by positivity
        nlinarith [hs0, h1, h2]
      have hid : κ / 2 * Real.sqrt t * (4 / κ) = 2 * Real.sqrt t := by
        field_simp
        ring
      have hmul := mul_le_mul_of_nonneg_left hge
        (by positivity : (0 : ℝ) ≤ κ / 2 * Real.sqrt t)
      rw [hid] at hmul
      calc 2 * Real.sqrt t ≤ κ / 2 * Real.sqrt t * Real.sqrt t := hmul
        _ = κ / 2 * t := by rw [mul_assoc, Real.mul_self_sqrt ht0]
    have hprod : Real.exp (2 * Real.sqrt t) * Real.exp (-(κ * t))
        ≤ Real.exp (-(κ / 2 * t)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      linarith
    calc t ^ n * Real.exp (2 * Real.sqrt t) * Real.exp (-(κ * t))
        = t ^ n * (Real.exp (2 * Real.sqrt t) * Real.exp (-(κ * t))) := by ring
      _ ≤ t ^ n * Real.exp (-(κ / 2 * t)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  exact squeeze_zero' hnonneg hle hmaj

end RHTower.Sieve
