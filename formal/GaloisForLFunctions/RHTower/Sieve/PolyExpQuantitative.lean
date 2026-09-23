import GaloisForLFunctions.RHTower.Sieve.ExpQuadraticQuantitative

/-!
# The ratio-form majorant, with a rate

`CoeffRatioBound.coeffMajorant_ratio_le` reduces the majorant at the chosen smoothing width to the
shape

    (1 + a(v²)⁹)(b + cv²)·exp(2v)·exp(-κv²) ,

and `ExpQuadraticDecay` shows that tends to zero.  Splitting the exponential and applying that limit
at `κ/2` gives the same statement with a rate:

    (1 + a(v²)⁹)(b + cv²)·exp(2v)·exp(-κv²) ≤ exp(-κv²/2)   for all large `v` .

This is the last of the three places where the contour argument discards its exponent.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **The ratio-form majorant against half the exponent.** -/
theorem eventually_poly_exp_two_sub_sq_le {a b c κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ v : ℝ in atTop,
      (1 + a * (v ^ (2 : ℕ)) ^ (9 : ℕ)) * (b + c * v ^ (2 : ℕ)) * Real.exp (2 * v) * Real.exp (-(κ * v ^ (2 : ℕ)))
        ≤ Real.exp (-(κ * v ^ (2 : ℕ) / 2)) := by
  have hhalf : (0 : ℝ) < κ / 2 := by linarith
  have h := tendsto_poly_exp_two_sub_sq (a := a) (b := b) (c := c) hhalf
  have h1 : ∀ᶠ v : ℝ in atTop,
      (1 + a * (v ^ (2 : ℕ)) ^ (9 : ℕ)) * (b + c * v ^ (2 : ℕ)) * Real.exp (2 * v)
          * Real.exp (-(κ / 2 * v ^ (2 : ℕ))) ≤ 1 := by
    have hlt := h.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hlt] with v hv
    exact le_of_lt hv
  filter_upwards [h1] with v hv
  have hpos : (0 : ℝ) < Real.exp (-(κ * v ^ (2 : ℕ) / 2)) := Real.exp_pos _
  have hsplit : Real.exp (-(κ * v ^ (2 : ℕ)))
      = Real.exp (-(κ / 2 * v ^ (2 : ℕ))) * Real.exp (-(κ * v ^ (2 : ℕ) / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  calc (1 + a * (v ^ (2 : ℕ)) ^ (9 : ℕ)) * (b + c * v ^ (2 : ℕ)) * Real.exp (2 * v)
        * (Real.exp (-(κ / 2 * v ^ (2 : ℕ))) * Real.exp (-(κ * v ^ (2 : ℕ) / 2)))
      = ((1 + a * (v ^ (2 : ℕ)) ^ (9 : ℕ)) * (b + c * v ^ (2 : ℕ)) * Real.exp (2 * v)
          * Real.exp (-(κ / 2 * v ^ (2 : ℕ)))) * Real.exp (-(κ * v ^ (2 : ℕ) / 2)) := by ring
    _ ≤ 1 * Real.exp (-(κ * v ^ (2 : ℕ) / 2)) := mul_le_mul_of_nonneg_right hv hpos.le
    _ = Real.exp (-(κ * v ^ (2 : ℕ) / 2)) := one_mul _

end RHTower.Sieve
