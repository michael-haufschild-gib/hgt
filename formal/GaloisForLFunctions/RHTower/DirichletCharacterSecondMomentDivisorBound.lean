/-
# Divisor-power form of the finite quadratic character second moment

This module connects the literal divisor-count second moment to the corpus's
proved explicit divisor bound.  It remains a finite odd square-free CRT
quadratic-character theorem; no zero-density, RH, GRH, or asymptotic input is
assumed.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterSecondMoment
import GaloisForLFunctions.RHTower.Sieve.DivisorBound

open Finset

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- Divisor-power version of the finite interval quadratic-character second moment.  The
constant is the fully constructed `RHTower.Sieve.divisorBoundConst ε`; no divisor-function
estimate is assumed. -/
theorem quadratic_intervalShiftSum_normSq_le_divisorRpow [DecidableEq I]
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∑ x : ZMod P.modulus, Complex.normSq (quadraticIntervalShiftSum P M b x) ≤
      ((M : ℝ) * (Sieve.divisorBoundConst ε * (P.modulus : ℝ) ^ ε) +
        (P.modulus : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
  have hdiv : (P.modulus.divisors.card : ℝ) ≤
      Sieve.divisorBoundConst ε * (P.modulus : ℝ) ^ ε :=
    Sieve.card_divisors_le_rpow hε P.modulus_neZero.out
  have henergy_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
    Finset.sum_nonneg fun k hk => sq_nonneg ‖b k‖
  calc
    _ ≤ ((M : ℝ) * (P.modulus.divisors.card : ℝ) + (P.modulus : ℝ)) *
        ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
      quadratic_intervalShiftSum_normSq_le_divisorCount P M b
    _ ≤ ((M : ℝ) * (Sieve.divisorBoundConst ε * (P.modulus : ℝ) ^ ε) +
        (P.modulus : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · simpa [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg M)) (P.modulus : ℝ)
      · exact henergy_nonneg

end OddPrimeFamily
end RHTower
