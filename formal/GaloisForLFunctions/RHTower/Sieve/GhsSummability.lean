import GaloisForLFunctions.RHTower.Sieve.GhsCoefficients
import GaloisForLFunctions.RHTower.Sieve.TripleConvolutionPerron

/-!
# Absolute convergence of the Granville–Harper–Soundararajan factors

A logarithm is `O(n^ε)` for every `ε > 0` — explicitly, `log x ≤ x^ε/ε` — so coefficients obeying
`‖a_n‖ ≤ C·log n` have abscissa of absolute convergence at most `1`.  Both prime weights of the
convolution are of that shape and `f` itself is bounded, so all three factors are `LSeriesSummable` on
every line `Re s = σ > 1`, and the triple Perron identity applies to them with no further hypothesis:

`2π ∑ₙ (a ⍟ (b ⍟ f))(n) w(n) = ∫_ℝ L(a,s_y)·L(b,s_y)·L(f,s_y)·W(s_y) dy`,   `s_y = σ + iy`.

This is the outer passage of step 4 of the argument, now stated for the sequences the log recursion
actually produces rather than for abstract summable factors.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Filter GaloisForLFunctions.HTGeometry

/-- **Logarithmically bounded coefficients converge absolutely to the right of `1`.**  A logarithm is
`O(n^ε)` for every `ε > 0`, so the abscissa of absolute convergence is at most `1`. -/
theorem LSeriesSummable_of_norm_le_const_mul_log {a : ℕ → ℂ} {C : ℝ}
    (hC : ∀ n : ℕ, ‖a n‖ ≤ C * Real.log n) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable a s := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := by
    have h := hC 2
    have h2 : (0 : ℝ) ≤ ‖a 2‖ := norm_nonneg _
    have : (0 : ℝ) ≤ C * Real.log 2 := by
      have hcast : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
      rw [hcast] at h
      linarith
    nlinarith [this, hlog2]
  set ε : ℝ := (s.re - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hxlt : 1 + ε < s.re := by rw [hε]; linarith
  refine LSeriesSummable_of_isBigO_rpow (x := 1 + ε) hxlt ?_
  refine Asymptotics.IsBigO.of_bound (C / ε) (Filter.Eventually.of_forall fun n => ?_)
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ε / ε := Real.log_le_rpow_div hnn hε0
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ ε := Real.rpow_nonneg hnn ε
  have hstep : ‖a n‖ ≤ C / ε * (n : ℝ) ^ ε := by
    refine (hC n).trans ?_
    calc C * Real.log (n : ℝ) ≤ C * ((n : ℝ) ^ ε / ε) :=
          mul_le_mul_of_nonneg_left hlog hC0
      _ = C / ε * (n : ℝ) ^ ε := by ring
  have hnorm : ‖((n : ℝ) ^ (1 + ε - 1) : ℝ)‖ = (n : ℝ) ^ ε := by
    rw [show (1 : ℝ) + ε - 1 = ε by ring, Real.norm_eq_abs, abs_of_nonneg hrpow]
  rw [hnorm]
  exact hstep

/-- The outer prime weight converges absolutely to the right of `1`. -/
theorem LSeriesSummable_ghsOuter {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (ghsOuter f N) s :=
  LSeriesSummable_of_norm_le_const_mul_log (C := 1 / Real.log 2) (norm_ghsOuter_le hf N) hs

/-- The inner prime weight converges absolutely to the right of `1`. -/
theorem LSeriesSummable_ghsInner {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (M : ℕ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (ghsInner f M) s :=
  LSeriesSummable_of_norm_le_const_mul_log (C := 1) (by simpa using norm_ghsInner_le hf M) hs

/-- **The Perron passage for the Granville–Harper–Soundararajan convolution.**  Every summability
hypothesis of the triple Perron identity is discharged for the three sequences the log recursion produces,
so the smoothed sum of the convolution *is* the vertical integral of the product of the three Dirichlet
series against the smoothing kernel — for any `f` with `‖f‖ ≤ 1` and any `σ > 1`. -/
theorem tsum_mul_smoothWeight_ghs_eq_integral {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N₀ M : ℕ)
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ) :
    (2 * Real.pi : ℝ) •
        (∑' n : ℕ, (LSeries.convolution (ghsOuter f N₀) (LSeries.convolution (ghsInner f M) f)) n
          * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (LSeries (ghsOuter f N₀) ((σ : ℂ) + (y : ℝ) * I)
              * LSeries (ghsInner f M) ((σ : ℂ) + (y : ℝ) * I)
            * LSeries f ((σ : ℂ) + (y : ℝ) * I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I) := by
  have hre : ((σ : ℂ)).re = σ := by simp
  have hs : 1 < ((σ : ℂ)).re := by rw [hre]; exact hσ
  exact tsum_mul_smoothWeight_convolution_eq_integral hN hH hσ
    (LSeriesSummable_ghsOuter hf N₀ hs) (LSeriesSummable_ghsInner hf M hs)
    (LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => hf n) hs)

end RHTower.Sieve
end
