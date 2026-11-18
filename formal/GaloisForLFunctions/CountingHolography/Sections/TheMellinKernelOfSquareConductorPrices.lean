import GaloisForLFunctions.CountingHolography.Sections.ThePrimeExponentsOnTheSquareDiagonal
import GaloisForLFunctions.CountingHolography.Sections.CriticalZerosSeparateThePrimeProfileFromFactorialKernels
import Mathlib.NumberTheory.LSeries.Deriv

/-! # Mellin scaling and the holomorphic error of the square prices

The factor two in the prime valuation cancels the Jacobian of the square
scale. Rounding the prime coordinates gives a Dirichlet series holomorphic
on Re s > 3, including after taking either part of each prime valuation.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticFunction _root_.RHTower
open scoped NNReal

/-- Mellin integral of one prime row in the conductor variable. The
parameter of the prime weight is s/2 − 1 in the conductor Dirichlet series. -/
theorem mellin_square_conductor_row {p : ℝ} (hp : 0<p) (s : ℂ) :
    mellin (fun t : ℝ => (2:ℂ)*squarePrimeWeight (p/t^2)) (2-s) =
      (p:ℂ)^(1-s/2)*mellin squarePrimeWeight (s/2-1) := by
  have he : (fun t : ℝ => (2:ℂ)*squarePrimeWeight (p/t^2)) =
      fun t : ℝ => (2:ℂ) • (fun x : ℝ => squarePrimeWeight (p*x)) (t^(-2:ℝ)) := by
    funext t
    have ht : t^(-2:ℝ)=(t^2)⁻¹ := by
      simpa only [Nat.cast_ofNat,zpow_neg,zpow_ofNat] using Real.rpow_neg_natCast t 2
    simp only [ht,div_eq_mul_inv,smul_eq_mul]
  rw [he,mellin_const_smul,mellin_comp_rpow,mellin_comp_mul_left _ _ hp]
  norm_num only [abs_neg,abs_two,Complex.ofReal_neg,Complex.ofReal_ofNat]
  rw [show (2-s)/(-2:ℂ)=s/2-1 by ring,show -(s/2-1)=1-s/2 by ring]
  simp only [smul_eq_mul,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_ofNat]
  ring

private abbrev S (n : ℕ) := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
private abbrev q (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)

/-- Coefficient of the error series when reading each exact valuation and
its prime profile through the same real function. -/
def squareValuationReadingError (g : ℝ → ℝ) (n : ℕ) : ℂ :=
  ((∑ p ∈ S n, (g (deningerRatExp (q n) p:ℝ)-g (diagonalPrimeProfile n p))*vonMangoldt p : ℝ):ℂ)

/-- Every Lipschitz reading has holomorphic Dirichlet error throughout
the half-plane to the right of three. This applies separately to the
logarithms of the reduced numerator, denominator and their ratio. -/
theorem analytic_squareValuationReadingError {g : ℝ → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    AnalyticOnNhd ℂ (LSeries (squareValuationReadingError g)) {s : ℂ | 3<s.re} := by
  obtain ⟨C,hC,h⟩ := diagonal_prime_exponent_profile_error
  have hbound (n : ℕ) (hn : n≠0) : ‖squareValuationReadingError g n‖≤((K:ℝ)*C)*(n:ℝ)^2 := by
    rw [squareValuationReadingError,Complex.norm_real,Real.norm_eq_abs]
    have hrow (p : ℕ) : |(g (deningerRatExp (q n) p:ℝ)-g (diagonalPrimeProfile n p))*vonMangoldt p| ≤
        K*(|(deningerRatExp (q n) p:ℝ)-diagonalPrimeProfile n p|*vonMangoldt p) := by
      rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.dist_eq] using
        hg.dist_le_mul (deningerRatExp (q n) p:ℝ) (diagonalPrimeProfile n p)) vonMangoldt_nonneg
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun p _ => hrow p)).trans ?_)
    rw [← mul_sum,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h (Nat.pos_of_ne_zero hn)) K.coe_nonneg
  have hab := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f := squareValuationReadingError g)
    (x := 2) ⟨K*C,fun n hn => by simpa only [Real.rpow_two] using hbound n hn⟩
  have h₃ : LSeries.abscissaOfAbsConv (squareValuationReadingError g)≤(3:EReal) := by
    convert hab using 1 <;> norm_num
  exact fun s hs => LSeries_analyticOnNhd _ s (h₃.trans_lt (by exact_mod_cast hs : (3:EReal)<(s.re:EReal)))

#print axioms mellin_square_conductor_row
#print axioms analytic_squareValuationReadingError

end GaloisForLFunctions.CountingHolography.Sections
