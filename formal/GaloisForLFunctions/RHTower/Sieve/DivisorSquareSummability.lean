import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Divisor-square inverse-power summability

The fixed second divisor moment is dominated coefficientwise by the fourth
Dirichlet-convolution power of zeta.  Absolute convergence of `ζ(s)^(4 : ℕ)` therefore gives the two
inverse-power summability statements needed for the moving-carrier affine mean-square argument.
-/

namespace RHTower.Sieve

open scoped ArithmeticFunction.zeta
open ArithmeticFunction Complex

private theorem zeta_pow_four_natCast (n : ℕ) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (4 : ℕ)) n : ℂ) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) ^ (4 : ℕ)) n := by
  have hzeta :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
        ArithmeticFunction ℂ) = ArithmeticFunction.zeta := by
    ext m
    simp [ArithmeticFunction.zeta_apply]
  have hpow : ∀ k : ℕ,
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ k :
          ArithmeticFunction ℕ) : ArithmeticFunction ℂ) =
        ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℂ) ^ k := by
    intro k
    induction k with
    | zero => exact ArithmeticFunction.natCoe_one
    | succ k ih =>
        rw [pow_succ, pow_succ, ArithmeticFunction.natCoe_mul, ih]
  exact DFunLike.congr_fun (hpow 4 |>.trans (by rw [hzeta])) n

/-- The fourth convolution power of zeta has an absolutely convergent L-series throughout
`re s > 1`. -/
theorem zetaPowFourLSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n : ℕ => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) ^ (4 : ℕ)) n) s := by
  have hz : LSeriesSummable
      (fun n : ℕ => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  simpa [pow_succ] using
    ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hz hz) hz) hz

/-- The divisor-square L-series converges absolutely throughout `re s > 1`.  This avoids every
pointwise `n^ε` loss. -/
theorem divisorSquareLSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n : ℕ => ((n.divisors.card ^ (2 : ℕ) : ℕ) : ℂ)) s := by
  have hz4 := zetaPowFourLSeriesSummable hs
  apply summable_norm_iff.mp
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => LSeries.norm_term_le s ?_) (summable_norm_iff.mpr hz4)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [Complex.norm_natCast]
    rw [← zeta_pow_four_natCast n, Complex.norm_natCast]
    exact_mod_cast card_divisors_pow_le_zeta_pow 2 n hn

/-- Weighted square coefficient mass used after the coarse moving-carrier derivative bound. -/
theorem summable_divisorSquare_div_sq :
    Summable (fun n : ℕ =>
      ((n.divisors.card : ℝ) ^ (2 : ℕ)) / ((n : ℝ) ^ (2 : ℕ))) := by
  have hnorm := summable_norm_iff.mpr
    (divisorSquareLSeriesSummable (s := (2 : ℂ)) (by norm_num))
  apply hnorm.congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp [LSeries.term_of_ne_zero hn]

/-- Unweighted square coefficient mass used after inserting the `n⁻¹/²` AFE coefficient. -/
theorem summable_divisorSquare_div_cube :
    Summable (fun n : ℕ =>
      ((n.divisors.card : ℝ) ^ (2 : ℕ)) / ((n : ℝ) ^ (3 : ℕ))) := by
  have hnorm := summable_norm_iff.mpr
    (divisorSquareLSeriesSummable (s := (3 : ℂ)) (by norm_num))
  apply hnorm.congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp [LSeries.term_of_ne_zero hn]

end RHTower.Sieve
