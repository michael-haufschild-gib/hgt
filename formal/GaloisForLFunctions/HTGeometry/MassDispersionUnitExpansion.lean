import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The principal-root expansion of the mass dispersion

For a real gauge `a > 0` and a spectral point `α` with `‖α‖² ≤ a²/2`, the principal root of
`a² + α²` differs from `a + α²/(2a)` by at most `‖α‖⁴/(3a³)`.

The proof is algebraic rather than asymptotic: with `S` the principal root and `A = a + α²/(2a)`,
the difference of squares gives `(S − A)(S + A) = −α⁴/(4a²)` exactly, while the principal branch
has nonnegative real part, so `‖S + A‖ ≥ Re A ≥ 3a/4`.  Dividing gives the bound with an explicit
constant and no hidden uniformity.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The principal complex square root has nonnegative real part. -/
theorem sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  have h : (Complex.sqrt z).re = Real.sqrt ((‖z‖ + z.re) / 2) := by
    simpa [Complex.sqrt] using Complex.cpow_inv_two_re (x := z)
  rw [h]
  exact Real.sqrt_nonneg _

/-- The principal root squares back. -/
theorem sq_sqrt (z : ℂ) : Complex.sqrt z ^ (2 : ℕ) = z :=
  Complex.cpow_nat_inv_pow _ (by norm_num)

/-- **The principal dispersion expansion with an explicit remainder.** -/
theorem norm_sqrt_sq_add_sub_le {a : ℝ} (ha : 0 < a) {alpha : ℂ}
    (hsmall : ‖alpha‖ ^ (2 : ℕ) ≤ a ^ (2 : ℕ) / 2) :
    ‖Complex.sqrt ((a : ℂ) ^ (2 : ℕ) + alpha ^ (2 : ℕ))
        - ((a : ℂ) + ((1 / (2 * a) : ℝ) : ℂ) * alpha ^ (2 : ℕ))‖
      ≤ ‖alpha‖ ^ (4 : ℕ) / (3 * a ^ (3 : ℕ)) := by
  set S : ℂ := Complex.sqrt ((a : ℂ) ^ (2 : ℕ) + alpha ^ (2 : ℕ)) with hSdef
  set A : ℂ := (a : ℂ) + ((1 / (2 * a) : ℝ) : ℂ) * alpha ^ (2 : ℕ) with hAdef
  have ha0 : ((a : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt ha
  have hsq : S ^ (2 : ℕ) = (a : ℂ) ^ (2 : ℕ) + alpha ^ (2 : ℕ) := sq_sqrt _
  have hcast : ((1 / (2 * a) : ℝ) : ℂ) = 1 / (2 * (a : ℂ)) := by
    push_cast
    ring
  have hkey : (S - A) * (S + A) = -(alpha ^ (4 : ℕ) / (4 * (a : ℂ) ^ (2 : ℕ))) := by
    have hexp : (S - A) * (S + A) = S ^ (2 : ℕ) - A ^ (2 : ℕ) := by ring
    rw [hexp, hsq, hAdef, hcast]
    field_simp
    ring
  -- the lower bound on the sum
  have hReA : 3 * a / 4 ≤ A.re := by
    have hre : A.re = a + (1 / (2 * a)) * (alpha ^ (2 : ℕ)).re := by
      rw [hAdef]
      simp [Complex.add_re, Complex.ofReal_re]
    have habs : |(alpha ^ (2 : ℕ)).re| ≤ ‖alpha‖ ^ (2 : ℕ) := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      rw [norm_pow]
    have hlow : -(‖alpha‖ ^ (2 : ℕ)) ≤ (alpha ^ (2 : ℕ)).re := neg_le_of_abs_le habs
    have hpos : 0 < 1 / (2 * a) := by positivity
    have hstep : (1 / (2 * a)) * (alpha ^ (2 : ℕ)).re ≥ (1 / (2 * a)) * (-(‖alpha‖ ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hlow hpos.le
    have hbound : (1 / (2 * a)) * (‖alpha‖ ^ (2 : ℕ)) ≤ a / 4 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hsmall, ha]
    rw [hre]
    nlinarith [hstep, hbound]
  have hReS : 0 ≤ S.re := sqrt_re_nonneg _
  have hsumlow : 3 * a / 4 ≤ ‖S + A‖ := by
    refine le_trans ?_ (Complex.re_le_norm (S + A))
    rw [Complex.add_re]
    linarith
  have hsumpos : 0 < ‖S + A‖ := lt_of_lt_of_le (by positivity) hsumlow
  have hnormkey : ‖S - A‖ * ‖S + A‖ = ‖alpha‖ ^ (4 : ℕ) / (4 * a ^ (2 : ℕ)) := by
    rw [← norm_mul, hkey, norm_neg, norm_div, norm_pow]
    congr 1
    rw [show (4 : ℂ) * (a : ℂ) ^ (2 : ℕ) = (((4 * a ^ (2 : ℕ) : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hfinal : ‖S - A‖ * (3 * a / 4) ≤ ‖alpha‖ ^ (4 : ℕ) / (4 * a ^ (2 : ℕ)) := by
    rw [← hnormkey]
    exact mul_le_mul_of_nonneg_left hsumlow (norm_nonneg _)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 3 * a ^ (3 : ℕ))]
  have hval : (4 * a ^ (2 : ℕ)) * (‖alpha‖ ^ (4 : ℕ) / (4 * a ^ (2 : ℕ))) = ‖alpha‖ ^ (4 : ℕ) := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hfinal (by positivity : (0 : ℝ) ≤ 4 * a ^ (2 : ℕ)), hval]

/-- **The principal dispersion expansion at a complex base point in the right half plane.**
`√(z² + a²) = z + a²/(2z) + O(|z|^{-3})` with an explicit constant, uniformly on every right
half plane. -/
theorem norm_sqrt_sq_add_sq_sub_le {z : ℂ} (hz : 0 < z.re) (a : ℝ) :
    ‖Complex.sqrt (z ^ (2 : ℕ) + ((a : ℝ) : ℂ) ^ (2 : ℕ)) - (z + ((a : ℝ) : ℂ) ^ (2 : ℕ) / (2 * z))‖
      ≤ a ^ (4 : ℕ) / (4 * z.re * ‖z‖ ^ (2 : ℕ)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hnormpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz0
  set S : ℂ := Complex.sqrt (z ^ (2 : ℕ) + ((a : ℝ) : ℂ) ^ (2 : ℕ)) with hSdef
  set A : ℂ := z + ((a : ℝ) : ℂ) ^ (2 : ℕ) / (2 * z) with hAdef
  have hsq : S ^ (2 : ℕ) = z ^ (2 : ℕ) + ((a : ℝ) : ℂ) ^ (2 : ℕ) := sq_sqrt _
  have hkey : (S - A) * (S + A) = -(((a : ℝ) : ℂ) ^ (4 : ℕ) / (4 * z ^ (2 : ℕ))) := by
    have hexp : (S - A) * (S + A) = S ^ (2 : ℕ) - A ^ (2 : ℕ) := by ring
    rw [hexp, hsq, hAdef]
    field_simp
    ring
  have hdivre : (((a : ℝ) : ℂ) ^ (2 : ℕ) / (2 * z)).re = a ^ (2 : ℕ) * z.re / (2 * ‖z‖ ^ (2 : ℕ)) := by
    have hns : Complex.normSq z = ‖z‖ ^ (2 : ℕ) := Complex.normSq_eq_norm_sq z
    rw [Complex.div_re]
    simp [Complex.normSq_mul, hns, pow_two]
    field_simp
  have hReA : z.re ≤ A.re := by
    rw [hAdef, Complex.add_re, hdivre]
    have : (0 : ℝ) ≤ a ^ (2 : ℕ) * z.re / (2 * ‖z‖ ^ (2 : ℕ)) := by positivity
    linarith
  have hReS : 0 ≤ S.re := sqrt_re_nonneg _
  have hsumlow : z.re ≤ ‖S + A‖ := by
    refine le_trans ?_ (Complex.re_le_norm (S + A))
    rw [Complex.add_re]
    linarith
  have hnormkey : ‖S - A‖ * ‖S + A‖ = a ^ (4 : ℕ) / (4 * ‖z‖ ^ (2 : ℕ)) := by
    rw [← norm_mul, hkey, norm_neg, norm_div]
    have h1 : ‖((a : ℝ) : ℂ) ^ (4 : ℕ)‖ = a ^ (4 : ℕ) := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, ← abs_pow,
        abs_of_nonneg (by positivity)]
    have h2 : ‖(4 : ℂ) * z ^ (2 : ℕ)‖ = 4 * ‖z‖ ^ (2 : ℕ) := by
      rw [norm_mul, norm_pow, show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num]
    rw [h1, h2]
  have hfinal : ‖S - A‖ * z.re ≤ a ^ (4 : ℕ) / (4 * ‖z‖ ^ (2 : ℕ)) := by
    rw [← hnormkey]
    exact mul_le_mul_of_nonneg_left hsumlow (norm_nonneg _)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * z.re * ‖z‖ ^ (2 : ℕ))]
  have hmul : (4 * ‖z‖ ^ (2 : ℕ)) * (a ^ (4 : ℕ) / (4 * ‖z‖ ^ (2 : ℕ))) = a ^ (4 : ℕ) := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hfinal (by positivity : (0 : ℝ) ≤ 4 * ‖z‖ ^ (2 : ℕ)), hmul]


end GaloisForLFunctions.HTGeometry
