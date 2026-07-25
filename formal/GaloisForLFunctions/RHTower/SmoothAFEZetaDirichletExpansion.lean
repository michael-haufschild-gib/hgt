import GaloisForLFunctions.RHTower.SmoothAFEZetaMellin

/-!
# Coefficient identification for the smooth zeta Mellin integral

This module converts the justified termwise integral from `SmoothAFEZetaMellin` into the canonical
Gaussian cutoff.  Positive-real complex-power algebra proves

`((a / b) : ℂ)⁻ʷ = a⁻ʷ bʷ`,

so each Dirichlet-series term factors as `(n+1)⁻ˢ` times the cutoff integrand at
`(n+1)/x`.  Consequently the normalized zeta Mellin integral equals the exact smoothed Dirichlet
series

`∑' n, (n+1)⁻ˢ V((n+1)/x)`.

This is the first half of the classical smooth approximate functional equation before the zeta
contour is shifted and reflected.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

theorem cpow_div_pos_neg
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℂ) :
    ((a / b : ℝ) : ℂ) ^ (-w) = (a : ℂ) ^ (-w) * (b : ℂ) ^ w := by
  have hab : 0 ≤ a / b := (div_pos ha hb).le
  have hmul := Complex.mul_cpow_ofReal_nonneg hab hb.le (-w)
  have hprod : ((a : ℂ) ^ (-w)) =
      ((a / b : ℝ) : ℂ) ^ (-w) * (b : ℂ) ^ (-w) := by
    convert hmul using 1
    norm_cast
    field_simp [hb.ne']
  have hb0 : (b : ℂ) ^ w ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))
  have hbinv : (b : ℂ) ^ (-w) * (b : ℂ) ^ w = 1 := by
    rw [Complex.cpow_neg]
    exact inv_mul_cancel₀ hb0
  calc
    ((a / b : ℝ) : ℂ) ^ (-w)
      = ((a / b : ℝ) : ℂ) ^ (-w) * 1 := by ring
    _ = ((a / b : ℝ) : ℂ) ^ (-w) *
        ((b : ℂ) ^ (-w) * (b : ℂ) ^ w) := by rw [hbinv]
    _ = (((a / b : ℝ) : ℂ) ^ (-w) * (b : ℂ) ^ (-w)) *
        (b : ℂ) ^ w := by ring
    _ = (a : ℂ) ^ (-w) * (b : ℂ) ^ w := by rw [← hprod]

theorem smoothAFEZetaMellinTerm_eq_cpow_mul_cutoffIntegrand
    {x : ℝ} (hx : 0 < x) (s : ℂ) (n : ℕ) (w : ℂ) :
    smoothAFEZetaMellinTerm s x n w =
      (n + 1 : ℂ) ^ (-s) *
        smoothAFEMellinIntegrand ((n + 1 : ℝ) / x) w := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [smoothAFEZetaMellinTerm, smoothAFEMellinIntegrand]
  rw [one_div, ← Complex.cpow_neg]
  rw [show -(s + w) = -s + -w by ring, Complex.cpow_add _ _ hn]
  rw [cpow_div_pos_neg (by exact_mod_cast Nat.succ_pos n) hx w]
  push_cast
  ring

theorem integral_smoothAFEZetaMellinTerm_eq_cpow_mul_cutoffIntegral
    {x c : ℝ} (hx : 0 < x) (s : ℂ) (n : ℕ) :
    (∫ t : ℝ, smoothAFEZetaMellinTerm s x n ((c : ℂ) + (t : ℂ) * I))
      = (n + 1 : ℂ) ^ (-s) * ∫ t : ℝ,
          smoothAFEMellinIntegrand ((n + 1 : ℝ) / x)
            ((c : ℂ) + (t : ℂ) * I) := by
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t =>
    smoothAFEZetaMellinTerm_eq_cpow_mul_cutoffIntegrand hx s n _

/-- Zeta-weighted Gaussian Mellin integral, normalized by `1 / (2π)`. -/
def smoothAFEZetaMellinAt (c : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ t : ℝ,
    smoothAFEZetaMellinIntegrand s x ((c : ℂ) + (t : ℂ) * I)

theorem smoothAFECutoffAt_eq_integral (c x : ℝ) :
    smoothAFECutoffAt c x = (1 / (2 * Real.pi)) • ∫ t : ℝ,
      smoothAFEMellinIntegrand x ((c : ℂ) + (t : ℂ) * I) := by
  rfl

theorem smoothAFEZetaMellinAt_eq_tsum_cutoff
    {s : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc : 1 < s.re + c) :
    smoothAFEZetaMellinAt c s x =
      ∑' n : ℕ, (n + 1 : ℂ) ^ (-s) *
        smoothAFECutoffAt c ((n + 1 : ℝ) / x) := by
  unfold smoothAFEZetaMellinAt
  rw [integral_smoothAFEZetaMellinIntegrand_eq_tsum hx hc hsc]
  rw [Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [integral_smoothAFEZetaMellinTerm_eq_cpow_mul_cutoffIntegral hx]
  rw [smoothAFECutoffAt_eq_integral]
  rw [Complex.real_smul]
  ring

theorem smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff
    {s : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc : 1 < s.re + c) :
    smoothAFEZetaMellinAt c s x =
      ∑' n : ℕ, (n + 1 : ℂ) ^ (-s) *
        smoothAFECutoff ((n + 1 : ℝ) / x) := by
  rw [smoothAFEZetaMellinAt_eq_tsum_cutoff hx hc hsc]
  apply tsum_congr
  intro n
  rw [smoothAFECutoffAt_eq_smoothAFECutoff
    (div_pos (by exact_mod_cast Nat.succ_pos n) hx) hc]

end RHTower
