import GaloisForLFunctions.HTGeometry.SmoothWeightPerron

/-!
# The Perron integrand is integrable for any coefficients

`integrable_perron_term` is stated for unit-bounded coefficients, but the hypothesis is not used for
anything integrability needs: the statement is about a *single* index `n`, so `‖a n‖` is a constant
and any value of it is absorbed into the majorant.

This matters for the Chebyshev route, whose coefficients are `Λ(n) ≤ log n` and therefore not
unit-bounded.  The version below has no hypothesis on the coefficients at all.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

/-- **Each Perron term is integrable, for arbitrary coefficients.** -/
theorem integrable_perron_term_general {a : ℕ → ℂ} (ha0 : a 0 = 0) {N H : ℝ} (hN : 0 < N)
    (hH : 0 < H) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Integrable (fun y : ℝ => a n * ((n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I)) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((σ : ℂ) + (y : ℝ) * Complex.I))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight_line hN hH hσ
  have hcont : Continuous (fun y : ℝ => a n * ((n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I)) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((σ : ℂ) + (y : ℝ) * Complex.I))) := by
    refine continuous_const.mul (Continuous.mul ?_ (continuous_mellin_smoothWeight_line hH hσ))
    exact Continuous.const_cpow (by fun_prop) (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (‖a n‖ * ((n : ℝ) ^ (-σ) * C)))
    hcont.aestronglyMeasurable ?_
  filter_upwards with y
  rw [norm_mul, norm_mul, norm_natCast_cpow_neg_line hn]
  calc ‖a n‖ * ((n : ℝ) ^ (-σ) *
        ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((σ : ℂ) + (y : ℝ) * Complex.I)‖)
      ≤ ‖a n‖ * ((n : ℝ) ^ (-σ) * (C * (1 + y ^ 2)⁻¹)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hbd y) hnn) (norm_nonneg _)
    _ = ‖a n‖ * ((n : ℝ) ^ (-σ) * C) * (1 + y ^ 2)⁻¹ := by ring

end RHTower.Sieve
