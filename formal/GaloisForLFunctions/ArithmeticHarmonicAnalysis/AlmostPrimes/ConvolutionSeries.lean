import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes.ConvolutionBounds
import GaloisForLFunctions.HTGeometry.DirichletConvolutionExponential

/-!
# Dirichlet series of almost-prime coefficients

The Dirichlet powers of von Mangoldt agree with the sequence convolution
powers. Their series is the corresponding power of `-ζ'/ζ` throughout
the half-plane of absolute convergence; their support starts at `2^k`.
-/

noncomputable section

open ArithmeticFunction
open scoped ArithmeticFunction
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes

theorem convolution_eq_dirichletConvPow (k n : ℕ) :
    (Λ ^ k) n = dirichletConvPow (fun m => Λ m) k n := by
  induction k generalizing n with
  | zero => simp only [pow_zero, ArithmeticFunction.one_apply, dirichletConvPow_zero_apply]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.mul_apply, dirichletConvPow_succ, LSeries.convolution_def]
    exact Finset.sum_congr rfl fun d _ => by rw [ih]

theorem complex_convolution_eq (k n : ℕ) :
    (((Λ ^ k) n : ℝ) : ℂ) = dirichletConvPow (fun m => (Λ m : ℂ)) k n := by
  rw [convolution_eq_dirichletConvPow, dirichletConvPow_ofReal]

/-- No product of `k` nontrivial prime powers lies below `2^k`. -/
theorem convolution_eq_zero_below (k n : ℕ) (hn : n < 2 ^ k) : (Λ ^ k) n = 0 := by
  rw [convolution_eq_dirichletConvPow]
  exact dirichletConvPow_eq_zero_of_lt (by simp) (by simp) k n hn

/-- The paper's almost-prime Dirichlet series, with absolute convergence proved. -/
theorem convolution_lseries (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (((Λ ^ k) n : ℝ) : ℂ)) s ∧
      LSeries (fun n => (((Λ ^ k) n : ℝ) : ℂ)) s =
        (-deriv riemannZeta s / riemannZeta s) ^ k := by
  simp_rw [complex_convolution_eq]
  have h := lseriesSummable_dirichletConvPow (LSeriesSummable_vonMangoldt hs) k
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at h
  exact h

#print axioms convolution_lseries
#print axioms convolution_eq_zero_below
#print axioms convolution_eq_zero_of_card_lt

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes
