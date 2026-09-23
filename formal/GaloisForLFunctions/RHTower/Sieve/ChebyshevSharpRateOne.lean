import GaloisForLFunctions.RHTower.Sieve.ChebyshevSharpTransferOne

/-!
# Removing the scalar and the bracket from the contour's conclusion

The contour bound controls `‖r·A - M·br‖`, where `r = 2π` is the scalar the Perron formula carries,
`A` is the smoothed sum, `M` the cutoff's mass and `br` the main term's bracket.  What a Chebyshev
estimate wants is `‖A - M‖`.

Since `r ≥ 1` the scalar only helps — `‖A - M‖ ≤ r‖A - M‖ = ‖r·A - M·r‖` — and the bracket is
removed by one triangle inequality against `‖M·br - M·r‖`, which is the mass times the bracket's
discrepancy.  Both steps are free of any analytic input.
-/

namespace RHTower.Sieve

open Complex

/-- **The scalar and the bracket come off.** -/
theorem norm_sub_le_of_scaled {A M br : ℂ} {r K₁ K₂ : ℝ} (hr : 1 ≤ r)
    (h1 : ‖(r : ℂ) * A - M * br‖ ≤ K₁) (h2 : ‖M * br - M * (r : ℂ)‖ ≤ K₂) :
    ‖A - M‖ ≤ K₁ + K₂ := by
  have hr0 : (0 : ℝ) < r := by linarith
  -- the scalar only helps
  have hscale : ‖(r : ℂ) * (A - M)‖ = r * ‖A - M‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hle : ‖A - M‖ ≤ ‖(r : ℂ) * (A - M)‖ := by
    rw [hscale]
    nlinarith [norm_nonneg (A - M), hr]
  -- the bracket comes off by one triangle inequality
  have hsplit : (r : ℂ) * (A - M) = (r : ℂ) * A - M * (r : ℂ) := by ring
  have htri : ‖(r : ℂ) * A - M * (r : ℂ)‖
      ≤ ‖(r : ℂ) * A - M * br‖ + ‖M * br - M * (r : ℂ)‖ := by
    have h := norm_add_le ((r : ℂ) * A - M * br) (M * br - M * (r : ℂ))
    rwa [sub_add_sub_cancel] at h
  rw [hsplit] at hle
  linarith [hle, htri, h1, h2]

/-- **The mass times the bracket's discrepancy.**  The difference of the two products is the mass
times the difference of the two real scalars. -/
theorem norm_mul_sub_mul_ofReal (M : ℂ) (a b : ℝ) :
    ‖M * ((a : ℝ) : ℂ) - M * ((b : ℝ) : ℂ)‖ = ‖M‖ * |a - b| := by
  rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **A square is absorbed at the contour's own rate**, halving the exponent once more. -/
theorem sq_mul_exp_neg_le' {s : ℝ} (hs : 0 ≤ s) :
    s ^ (2 : ℕ) * Real.exp (-(s / 480000)) ≤ 4 * 960000 ^ (2 : ℕ) * Real.exp (-(s / 960000)) := by
  have hbound := sq_le_exp_div_gen hs (k := 960000) (by norm_num)
  have hexp : Real.exp (s / 960000) * Real.exp (-(s / 480000))
      = Real.exp (-(s / 960000)) := by
    rw [← Real.exp_add]
    ring_nf
  have hpos : (0 : ℝ) < Real.exp (-(s / 480000)) := Real.exp_pos _
  calc s ^ (2 : ℕ) * Real.exp (-(s / 480000))
      ≤ 4 * 960000 ^ (2 : ℕ) * Real.exp (s / 960000) * Real.exp (-(s / 480000)) :=
        mul_le_mul_of_nonneg_right hbound hpos.le
    _ = 4 * 960000 ^ (2 : ℕ) * (Real.exp (s / 960000) * Real.exp (-(s / 480000))) := by ring
    _ = 4 * 960000 ^ (2 : ℕ) * Real.exp (-(s / 960000)) := by rw [hexp]

end RHTower.Sieve
