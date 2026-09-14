import GaloisForLFunctions.RHTower.Sieve.KloostermanCompleteColumnCorrelation
import GaloisForLFunctions.RHTower.Sieve.StadlmannReciprocalPhaseApplications
import GaloisForLFunctions.RHTower.Sieve.KloostermanRamanujanDivisorSum

/-!
# Complete Kloosterman columns as Ramanujan coefficients

The complete equal-modulus column correlation is the modulus times the corpus's
Chen--Gupta--Li Ramanujan coefficient.  The exact gcd--Möbius divisor formula then makes its
arithmetic dependence explicit.  A direct triangle estimate records an unconditional divisor-sum
majorant without introducing any analytic hypothesis.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem norm_moebius_intCast_complex_le_one (a : ℕ) :
    ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)

/-- Complete equal-modulus column correlation is a scaled CGL Ramanujan coefficient. -/
theorem kloostermanCompleteColumnCorrelation_eq_cglRamanujan
    (q : ℕ) [NeZero q] (n k : ZMod q) :
    kloostermanCompleteColumnCorrelation q n k =
      (q : ℂ) * RHTower.cglRamanujanAdditiveSum
        ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ (k - n) := by
  rw [kloostermanCompleteColumnCorrelation_eq,
    ← stadlmannReciprocalPhaseSum_eq_kloosterman,
    stadlmannReciprocalPhaseSum_eq_cglRamanujan]

/-- Exact gcd--Möbius divisor formula for complete equal-modulus column correlation. -/
theorem kloostermanCompleteColumnCorrelation_eq_gcd_mobiusDivisorSum
    (q : ℕ) [NeZero q] (n k : ZMod q) :
    kloostermanCompleteColumnCorrelation q n k =
      (q : ℂ) *
        ∑ d ∈ ((k - n).val.gcd q).divisors,
          (d : ℂ) *
            ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) := by
  rw [kloostermanCompleteColumnCorrelation_eq_cglRamanujan,
    cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum_sieve]

/-- Unconditional divisor-sum majorant for complete equal-modulus column correlation. -/
theorem norm_kloostermanCompleteColumnCorrelation_le_divisorSum
    (q : ℕ) [NeZero q] (n k : ZMod q) :
    ‖kloostermanCompleteColumnCorrelation q n k‖ ≤
      (q : ℝ) * ∑ d ∈ ((k - n).val.gcd q).divisors, (d : ℝ) := by
  rw [kloostermanCompleteColumnCorrelation_eq_gcd_mobiusDivisorSum,
    norm_mul, Complex.norm_natCast]
  gcongr
  calc
    ‖∑ d ∈ ((k - n).val.gcd q).divisors,
        (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)‖ ≤
        ∑ d ∈ ((k - n).val.gcd q).divisors,
          ‖(d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ ((k - n).val.gcd q).divisors, (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_natCast]
      nlinarith [norm_moebius_intCast_complex_le_one (q / d)]

end

end RHTower.Sieve
