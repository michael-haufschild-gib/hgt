import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerPrimeSplit

/-!
# The retained Euler coefficients are driven by the deleted primes

The coprime indicator evolves under surviving-prime force. Its dual
finite Euler product evolves under minus the deleted-prime force. Both
equations follow from the same logarithmic derivation and the exact
factorization `a * zeta = rho`; no prime force is omitted.
-/

noncomputable section

namespace RHTower

/-- The finite Euler product has the complementary logarithmic derivative. -/
theorem logDerivation_ccmEulerMobius (P : ℕ) :
    logDerivation (ccmEulerMobius P) =
      -(ccmEulerMobius P * ccmEulerDeletedPrime P) := by
  have h := congrArg logDerivation (ccmEulerMobius_mul_zeta P)
  rw [logDerivation_mul, logDerivation_zeta] at h
  change logDerivation (ccmEulerMobius P) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) +
    ccmEulerMobius P * ArithmeticFunction.log = logDerivation (ccmEulerCoprime P) at h
  rw [logDerivation_ccmEulerCoprime, ccmEulerCoprime, ← ccmEulerMobius_mul_zeta P,
    ← ArithmeticFunction.zeta_mul_vonMangoldt, ← ccmEuler_prime_split P] at h
  have hz : (logDerivation (ccmEulerMobius P) + ccmEulerMobius P * ccmEulerDeletedPrime P) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 0 := by
    linear_combination h
  have hi := congrArg (fun f : ArithmeticFunction ℝ =>
    f * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) hz
  rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one, zero_mul] at hi
  exact eq_neg_of_add_eq_zero_left hi

/-- Coefficient form of the exact deleted-prime force. -/
theorem ccmEulerMobius_mul_deletedPrime (P n : ℕ) :
    (ccmEulerMobius P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n =
      -ccmEulerMobius P n * Real.log n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (logDerivation_ccmEulerMobius P)
  rw [logDerivation_apply, ArithmeticFunction.neg_apply] at h
  linarith only [h]

/-- The second generator retains the derivative of the deleted-prime force. -/
theorem logDerivation_sq_ccmEulerMobius (P : ℕ) :
    logDerivation (logDerivation (ccmEulerMobius P)) =
      ccmEulerMobius P * (ccmEulerDeletedPrime P * ccmEulerDeletedPrime P) -
        ccmEulerMobius P * logDerivation (ccmEulerDeletedPrime P) := by
  rw [logDerivation_ccmEulerMobius, logDerivation_neg, logDerivation_mul,
    logDerivation_ccmEulerMobius]
  ring

/-- The full prime force is the difference of the two complementary generators. -/
theorem ccmEuler_prime_generator_balance (P : ℕ) :
    ccmEulerMobius P * logDerivation (ccmEulerCoprime P) -
      logDerivation (ccmEulerMobius P) * ccmEulerCoprime P =
        (ccmEulerMobius P * ccmEulerCoprime P) * ArithmeticFunction.vonMangoldt := by
  rw [logDerivation_ccmEulerCoprime, logDerivation_ccmEulerMobius,
    ← ccmEuler_prime_split P]
  ring

end RHTower
