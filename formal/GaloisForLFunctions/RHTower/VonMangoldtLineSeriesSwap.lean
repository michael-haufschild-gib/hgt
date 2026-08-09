import GaloisForLFunctions.RHTower.XiRelativeResolventFlux

/-!
# Termwise von Mangoldt integration along a vertical line

On a vertical line `s = σ + it` with `σ > 1`, the von Mangoldt `LSeries` may be integrated
termwise against any integrable weight: the integral of the series equals the sum of the
integrals.  The domination is exact — each term's integral norm is `Λ(n)·n^{−σ}·‖F‖₁` — and the
prime-side summability is the classical `σ > 1` convergence.

This is the first stage of the prime-side certification of the eigen-pair Guinand–Weil
identity: the swap that turns the line integral of the log-derivative's Dirichlet series against
a test kernel into a sum of single-frequency integrals.
-/

namespace RHTower

noncomputable section

open MeasureTheory Complex ArithmeticFunction

/-- Real summability of the von Mangoldt weights at exponent `σ > 1`. -/
theorem summable_vonMangoldt_mul_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
  have hs : LSeriesSummable (fun n => (vonMangoldt n : ℂ)) (σ : ℂ) :=
    LSeriesSummable_vonMangoldt (by simpa using hσ)
  rw [LSeriesSummable] at hs
  rw [← Complex.summable_ofReal]
  refine hs.congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hcast : ((vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) =
        (vonMangoldt n : ℂ) / (n : ℂ) ^ (σ : ℂ) := by
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv]
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) σ]
      norm_cast
    rw [LSeries.term_of_ne_zero hn, hcast]

/-- The single-frequency line kernel in exponential form. -/
theorem natCast_cpow_neg_line_eq (n : ℕ) (hn : n ≠ 0) (σ t : ℝ) :
    (n : ℂ) ^ (-(σ + t * I) : ℂ) =
      Complex.exp (Complex.log (n : ℂ) * (-(σ + t * I))) := by
  exact Complex.cpow_def_of_ne_zero (by exact_mod_cast hn) _

/-- The line kernel is continuous in the frequency variable. -/
theorem continuous_line_kernel (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    Continuous fun t : ℝ => (n : ℂ) ^ (-(σ + t * I) : ℂ) := by
  have hrw : (fun t : ℝ => (n : ℂ) ^ (-(σ + t * I) : ℂ)) =
      fun t : ℝ => Complex.exp (Complex.log (n : ℂ) * (-(σ + t * I))) :=
    funext fun t => natCast_cpow_neg_line_eq n hn σ t
  rw [hrw]
  exact Complex.continuous_exp.comp <| continuous_const.mul <|
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg

/-- The line kernel has constant modulus `n^{−σ}` along the line. -/
theorem norm_line_kernel (n : ℕ) (hn : n ≠ 0) (σ t : ℝ) :
    ‖(n : ℂ) ^ (-(σ + t * I) : ℂ)‖ = (n : ℝ) ^ (-σ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log hnpos.le]
  have hre_full : (Complex.log (n : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))).re =
      Real.log (n : ℝ) * (-σ) := by
    rw [hlog, Complex.re_ofReal_mul]
    congr 1
    simp
  rw [natCast_cpow_neg_line_eq n hn σ t, Complex.norm_exp, hre_full,
    Real.rpow_def_of_pos hnpos]

/-- Each von Mangoldt line term against an integrable weight is integrable. -/
theorem integrable_vonMangoldt_line_term {σ : ℝ} {F : ℝ → ℂ} (hF : Integrable F) (n : ℕ) :
    Integrable (fun t : ℝ =>
      LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ + t * I) n * F t) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, zero_mul]
    exact integrable_zero _ _ _
  · have hterm : ∀ t : ℝ,
        LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ + t * I) n =
          (vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ + t * I) : ℂ) := by
      intro t
      rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
    have hbound : ∀ᵐ t : ℝ ∂volume,
        ‖(vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ + t * I) : ℂ)‖ ≤
          vonMangoldt n * (n : ℝ) ^ (-σ) := by
      filter_upwards with t
      rw [norm_mul, norm_line_kernel n hn σ t, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => (vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ + t * I) : ℂ)) volume :=
      (continuous_const.mul (continuous_line_kernel n hn σ)).aestronglyMeasurable
    have h := hF.bdd_mul hmeas hbound
    refine h.congr ?_
    filter_upwards with t
    rw [hterm t]

/-- The exact integral-norm value of each line term. -/
theorem integral_norm_vonMangoldt_line_term {σ : ℝ} {F : ℝ → ℂ} (n : ℕ) :
    (∫ t : ℝ, ‖LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ + t * I) n * F t‖) =
      vonMangoldt n * (n : ℝ) ^ (-σ) * ∫ t : ℝ, ‖F t‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · have hpt : ∀ t : ℝ,
        ‖LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ + t * I) n * F t‖ =
          vonMangoldt n * (n : ℝ) ^ (-σ) * ‖F t‖ := by
      intro t
      have hs_re : (((σ : ℂ) + (t : ℂ) * I)).re = σ := by simp
      rw [LSeries.term_of_ne_zero hn, norm_mul, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hs_re,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
        Real.rpow_neg (Nat.cast_nonneg n)]
      ring
    calc (∫ t : ℝ, ‖LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ + t * I) n * F t‖)
        = ∫ t : ℝ, vonMangoldt n * (n : ℝ) ^ (-σ) * ‖F t‖ := by
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = vonMangoldt n * (n : ℝ) ^ (-σ) * ∫ t : ℝ, ‖F t‖ := integral_const_mul _ _

/-- **Termwise von Mangoldt line integration.**  On `σ > 1`, the line integral of the von
Mangoldt `LSeries` against any integrable weight is the sum of the single-frequency
integrals. -/
theorem integral_LSeries_vonMangoldt_mul_eq_tsum {σ : ℝ} (hσ : 1 < σ) {F : ℝ → ℂ}
    (hF : Integrable F) :
    (∫ t : ℝ, LSeries (fun m => (vonMangoldt m : ℂ)) (σ + t * I) * F t) =
      ∑' n : ℕ, ∫ t : ℝ,
        LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ + t * I) n * F t := by
  have hpt : (fun t : ℝ => LSeries (fun m => (vonMangoldt m : ℂ)) (σ + t * I) * F t) =
      fun t : ℝ => ∑' n : ℕ,
        LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ + t * I) n * F t := by
    funext t
    rw [LSeries, tsum_mul_right]
  rw [hpt]
  refine (integral_tsum_of_summable_integral_norm
    (fun n => integrable_vonMangoldt_line_term hF n) ?_).symm
  have hval : (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ + t * I) n * F t‖) =
        fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-σ) * ∫ t : ℝ, ‖F t‖ := by
    funext n
    exact integral_norm_vonMangoldt_line_term n
  rw [hval]
  exact (summable_vonMangoldt_mul_rpow hσ).mul_right _

end

end RHTower
