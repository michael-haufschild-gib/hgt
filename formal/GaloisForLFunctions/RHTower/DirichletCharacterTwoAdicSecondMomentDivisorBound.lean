/-
# Divisor-power level-four/odd quadratic-character second moment

This closes the elementary divisor-growth reduction for the level-four/odd
CRT character, using the corpus's proved explicit divisor estimate.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicSecondMoment
import GaloisForLFunctions.RHTower.DirichletCharacterSecondMomentDivisorBound

open Finset

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- Divisor-power form of the fully closed level-four/odd finite second moment.  For every
positive exponent, `Sieve.divisorBoundConst ε` is a constructed corpus constant, so this theorem
has no unproved analytic premise. -/
theorem fourOdd_quadratic_intervalShiftSum_normSq_le_divisorRpow [DecidableEq I]
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∑ x : ZMod (fourOddModulus P),
      Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) ≤
      4 * (((M : ℝ) * (Sieve.divisorBoundConst ε * (fourOddModulus P : ℝ) ^ ε) +
        (fourOddModulus P : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2) := by
  have hdiv : ((fourOddModulus P).divisors.card : ℝ) ≤
      Sieve.divisorBoundConst ε * (fourOddModulus P : ℝ) ^ ε :=
    Sieve.card_divisors_le_rpow hε (fourOddModulus_neZero P).out
  have henergy_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
    Finset.sum_nonneg fun k hk => sq_nonneg ‖b k‖
  calc
    _ ≤ 4 * (((M : ℝ) * ((fourOddModulus P).divisors.card : ℝ) +
        (fourOddModulus P : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2) :=
      fourOdd_quadratic_intervalShiftSum_normSq_le_divisorCount P M b
    _ ≤ 4 * (((M : ℝ) * (Sieve.divisorBoundConst ε * (fourOddModulus P : ℝ) ^ ε) +
        (fourOddModulus P : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_right
        · simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg M))
              (fourOddModulus P : ℝ)
        · exact henergy_nonneg
      · norm_num

end OddPrimeFamily
end RHTower
