import GaloisForLFunctions.RHTower.PerronWeightedKernel
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The smoothed Perron explicit formula

For `x > 0` and `a > 1`,

`∑ Λ(n)·(log(x/n))⁺ = ∫ (−ζ′/ζ)(a+2πiw)·x^{a+2πiw}/(a+2πiw)² dw`.

Each term is the weighted Perron kernel at `u = log(x/n)`; the swap of
sum and integral is absolutely convergent because the integrand's norm
is `Λ(n)·(x/n)^a/(a²+(2πw)²)` and `∑ Λ(n) n^{-a}` converges for
`a > 1`; the resulting integrand sums to the von Mangoldt L-series,
which is `−ζ′/ζ` on `Re s > 1`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter ArithmeticFunction

/-- The quadratic comparison `1 + w² ≤ (1/a² + 1/4π²)·(a² + (2πw)²)`. -/
private theorem one_add_sq_le {a : ℝ} (ha : 0 < a) (w : ℝ) :
    1 + w ^ 2 ≤ (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2))
      * (a ^ 2 + (2 * Real.pi * w) ^ 2) := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2)) * a ^ 2
      = 1 + a ^ 2 / (4 * Real.pi ^ 2) := by
    field_simp
  have h2 : (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2)) * (2 * Real.pi * w) ^ 2
      = (2 * Real.pi * w) ^ 2 / a ^ 2 + w ^ 2 := by
    field_simp
    ring
  have hdist : (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2))
        * (a ^ 2 + (2 * Real.pi * w) ^ 2)
      = (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2)) * a ^ 2
        + (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2)) * (2 * Real.pi * w) ^ 2 := by
    ring
  have h3 : (0 : ℝ) ≤ a ^ 2 / (4 * Real.pi ^ 2) := by positivity
  have h4 : (0 : ℝ) ≤ (2 * Real.pi * w) ^ 2 / a ^ 2 := by positivity
  linarith [h1, h2, hdist, h3, h4]

/-- Norm of the weighted Perron integrand:
`‖e^{su}/s²‖ = e^{au}/(a²+(2πw)²)` for `s = a + 2πiw`. -/
theorem norm_perron_integrand {a : ℝ} (u w : ℝ) :
    ‖Complex.exp (((a : ℂ) + 2 * Real.pi * w * Complex.I) * ((u : ℝ) : ℂ))
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖
      = Real.exp (a * u) / (a ^ 2 + (2 * Real.pi * w) ^ 2) := by
  rw [norm_div, Complex.norm_exp, norm_pow]
  rw [show (a : ℂ) + 2 * Real.pi * w * Complex.I
      = ((a : ℝ) : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  congr 1
  simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]

/-- Integrability of the weighted Perron integrand. -/
theorem integrable_perron_integrand {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Integrable (fun w : ℝ =>
      Complex.exp (((a : ℂ) + 2 * Real.pi * w * Complex.I) * ((u : ℝ) : ℂ))
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hg : Integrable (fun w : ℝ =>
      (Real.exp (a * u) * (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2)))
        * (1 + w ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hcne : ∀ w : ℝ, ((a : ℂ) + 2 * Real.pi * w * Complex.I) ≠ 0 := by
    intro w h
    have h2 := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im] at h2
    linarith
  apply Integrable.mono hg
  · apply Continuous.aestronglyMeasurable
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro w
      exact pow_ne_zero 2 (hcne w)
  · filter_upwards with w
    rw [norm_perron_integrand]
    have hgn : ‖Real.exp (a * u) * (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2))
          * (1 + w ^ 2)⁻¹‖
        = Real.exp (a * u) * (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2))
          * (1 + w ^ 2)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hgn]
    have hle := one_add_sq_le ha w
    have h2 : (1 : ℝ) ≤ (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2))
        * (1 + w ^ 2)⁻¹ * (a ^ 2 + (2 * Real.pi * w) ^ 2) := by
      rw [show (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2)) * (1 + w ^ 2)⁻¹
            * (a ^ 2 + (2 * Real.pi * w) ^ 2)
          = ((1 / a ^ 2 + 1 / (4 * Real.pi ^ 2))
            * (a ^ 2 + (2 * Real.pi * w) ^ 2)) * (1 + w ^ 2)⁻¹ from by
        ring]
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact hle
    rw [div_le_iff₀ (by positivity)]
    calc Real.exp (a * u) = Real.exp (a * u) * 1 := (mul_one _).symm
      _ ≤ Real.exp (a * u) * ((1 / a ^ 2 + 1 / (4 * Real.pi ^ 2))
            * (1 + w ^ 2)⁻¹ * (a ^ 2 + (2 * Real.pi * w) ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
      _ = Real.exp (a * u) * (1 / a ^ 2 + 1 / (4 * Real.pi ^ 2))
            * (1 + w ^ 2)⁻¹ * (a ^ 2 + (2 * Real.pi * w) ^ 2) := by
        ring

/-- The Perron–von Mangoldt term `Λ(n)·e^{s·log(x/n)}/s²`,
`s = a + 2πiw`. -/
def perronVonMangoldtTerm (a x : ℝ) (n : ℕ) (w : ℝ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
    * (Complex.exp (((a : ℂ) + 2 * Real.pi * w * Complex.I)
        * ((Real.log (x / n) : ℝ) : ℂ))
      / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)

/-- Absolute integral summability of the actual von Mangoldt Perron terms.
This majorant also controls character twists term by term. -/
theorem summable_integral_norm_perronVonMangoldtTerm {x a : ℝ} (hx : 0 < x)
    (ha : 1 < a) :
    Summable (fun n : ℕ => ∫ w : ℝ, ‖perronVonMangoldtTerm a x n w‖) := by
  have hnormint : ∀ n : ℕ, (∫ w : ℝ, ‖perronVonMangoldtTerm a x n w‖)
      = ArithmeticFunction.vonMangoldt n
        * Real.exp (a * Real.log (x / n))
        * ∫ w : ℝ, (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ := by
    intro n
    have heqn : ∀ w : ℝ, ‖perronVonMangoldtTerm a x n w‖
        = (ArithmeticFunction.vonMangoldt n
            * Real.exp (a * Real.log (x / n)))
          * (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ := by
      intro w
      unfold perronVonMangoldtTerm
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg, norm_perron_integrand,
        div_eq_mul_inv]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall heqn),
      integral_const_mul]
  have hsum : Summable
      (fun n : ℕ => ∫ w : ℝ, ‖perronVonMangoldtTerm a x n w‖) := by
    have hLS := ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := ((a : ℝ) : ℂ)) (by rwa [Complex.ofReal_re])
    have hns : Summable (fun n : ℕ =>
        ‖LSeries.term (fun m : ℕ =>
          ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) ((a : ℝ) : ℂ) n‖) :=
      summable_norm_iff.2 hLS
    have hterm_norm : ∀ n : ℕ,
        ‖LSeries.term (fun m : ℕ =>
          ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) ((a : ℝ) : ℂ) n‖
        = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ a := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [LSeries.term_def, ArithmeticFunction.map_zero]
      · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
        rw [LSeries.term_def, if_neg (Nat.pos_iff_ne_zero.1 hn), norm_div,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg vonMangoldt_nonneg,
          show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) from
            (Complex.ofReal_natCast n).symm,
          Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.ofReal_re]
    have hreal : Summable (fun n : ℕ =>
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ a) :=
      hns.congr hterm_norm
    apply (hreal.mul_left
      ((x ^ a) * ∫ w : ℝ, (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹)).congr
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hnormint 0]
      simp [ArithmeticFunction.map_zero]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
      rw [hnormint n,
        show Real.exp (a * Real.log (x / n)) = (x / n) ^ a from by
          rw [Real.rpow_def_of_pos (div_pos hx hn0), mul_comm],
        Real.div_rpow hx.le (Nat.cast_nonneg n)]
      ring
  exact hsum

/-- The literal Perron term is its Dirichlet-series term times the common kernel. -/
theorem perronVonMangoldtTerm_eq_LSeries_term {x a : ℝ} (hx : 0 < x) (w : ℝ) :
    ∀ n : ℕ, perronVonMangoldtTerm a x n w
        = LSeries.term (fun m : ℕ =>
            ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
            ((a : ℂ) + 2 * Real.pi * w * Complex.I) n
          * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
            / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold perronVonMangoldtTerm
    simp [LSeries.term_def, ArithmeticFunction.map_zero]
  · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
    have hxn : (0 : ℝ) < x / n := div_pos hx hn0
    have h1 : Complex.exp (((a : ℂ) + 2 * Real.pi * w * Complex.I)
          * ((Real.log (x / n) : ℝ) : ℂ))
        = ((x / n : ℝ) : ℂ)
          ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero
          (Complex.ofReal_ne_zero.2 (ne_of_gt hxn)),
        ← Complex.ofReal_log hxn.le]
      congr 1
      ring
    have h2 : ((x / n : ℝ) : ℂ)
          ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        = (x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          * (((n : ℕ) : ℂ)
            ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I))⁻¹ := by
      rw [show ((x / (n : ℝ) : ℝ) : ℂ)
          = ((x : ℝ) : ℂ) * ((((n : ℝ))⁻¹ : ℝ) : ℂ) from by
        push_cast; ring]
      rw [Complex.mul_cpow_ofReal_nonneg hx.le
        (inv_nonneg.2 (Nat.cast_nonneg n))]
      rw [Complex.ofReal_inv]
      rw [Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
        exact Real.pi_ne_zero.symm)]
      rw [Complex.ofReal_natCast]
    unfold perronVonMangoldtTerm
    rw [h1, h2, LSeries.term_def, if_neg (Nat.pos_iff_ne_zero.1 hn)]
    ring

/-- **The smoothed Perron explicit formula**: for `x > 0`, `a > 1`,
`∑ Λ(n)·(log(x/n))⁺ = ∫ (−ζ′/ζ)(a+2πiw)·x^{a+2πiw}/(a+2πiw)² dw`. -/
theorem smoothed_chebyshev_eq_perron_integral {x a : ℝ} (hx : 0 < x)
    (ha : 1 < a) :
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
        * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)
      = ∫ w : ℝ,
          (- deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I))
            * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  -- each term is a weighted Perron kernel integral
  have hstep1 : ∀ n : ℕ,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
          * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)
        = ∫ w : ℝ, perronVonMangoldtTerm a x n w := by
    intro n
    unfold perronVonMangoldtTerm
    rw [integral_const_mul, perron_weighted_kernel ha0]
  -- integrability of each term
  have hint : ∀ n : ℕ, Integrable (perronVonMangoldtTerm a x n) := by
    intro n
    unfold perronVonMangoldtTerm
    exact (integrable_perron_integrand ha0 (Real.log (x / n))).const_mul _
  -- the integrated norms are summable
  have hsum := summable_integral_norm_perronVonMangoldtTerm hx ha
  -- the pointwise sum is the von Mangoldt L-series
  have hstep3 : ∀ w : ℝ, (∑' n : ℕ, perronVonMangoldtTerm a x n w)
      = (- deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I))
        * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
    intro w
    have hre : ((a : ℂ) + 2 * Real.pi * w * Complex.I).re = a := by
      simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
    have hterm := perronVonMangoldtTerm_eq_LSeries_term (a := a) hx w
    calc ∑' n : ℕ, perronVonMangoldtTerm a x n w
        = ∑' n : ℕ, LSeries.term (fun m : ℕ =>
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
              ((a : ℂ) + 2 * Real.pi * w * Complex.I) n
            * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) :=
          tsum_congr hterm
      _ = (∑' n : ℕ, LSeries.term (fun m : ℕ =>
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
              ((a : ℂ) + 2 * Real.pi * w * Complex.I) n)
            * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) :=
          tsum_mul_right
      _ = (- deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I))
            * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
          rw [show (∑' n : ℕ, LSeries.term (fun m : ℕ =>
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
              ((a : ℂ) + 2 * Real.pi * w * Complex.I) n)
            = LSeries (fun m : ℕ =>
                ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
                ((a : ℂ) + 2 * Real.pi * w * Complex.I) from rfl]
          rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div
            (by rw [hre]; exact ha)]
  calc ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
        * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)
      = ∑' n : ℕ, ∫ w : ℝ, perronVonMangoldtTerm a x n w :=
        tsum_congr hstep1
    _ = ∫ w : ℝ, ∑' n : ℕ, perronVonMangoldtTerm a x n w :=
        integral_tsum_of_summable_integral_norm hint hsum
    _ = ∫ w : ℝ,
          (- deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I))
            * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) :=
        integral_congr_ae (Filter.Eventually.of_forall hstep3)

end RHTower
