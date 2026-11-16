import GaloisForLFunctions.HilbertMetric.QuantumWalk.Compression

/-!
# Polynomial calculus on a projection

The complementary-sector decomposition used in Bhakta–Bhattacharjya,
equation (4.5), reduces polynomial calculus on an idempotent to evaluations
at zero and one. In a compressed space its complementary identity is `Q-E`.
-/

namespace GaloisForLFunctions.HilbertMetric.QuantumWalk
open Polynomial
variable {𝕜 R : Type*} [CommRing 𝕜] [Ring R] [Algebra 𝕜 R]

/-- Polynomial evaluation on an idempotent splits into its two spectral sectors. -/
theorem aeval_idempotent (E : R) (hE : E * E = E) (p : 𝕜[X]) :
    aeval E p = p.eval 1 • E + p.eval 0 • (1 - E) := by
  have hpow (n : ℕ) : E ^ (n + 1) = E := by
    induction n with
    | zero => exact pow_one E
    | succ n ih => rw [pow_succ, ih, hE]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hp, hq, eval_add, add_smul]
    abel
  | monomial n a =>
    cases n with
    | zero =>
      simp only [aeval_monomial, eval_monomial, pow_zero, mul_one]
      rw [← smul_add, add_sub_cancel, Algebra.smul_def, mul_one]
    | succ n =>
      simp only [aeval_monomial, hpow, eval_monomial, one_pow, mul_one,
        zero_pow (Nat.succ_ne_zero n), mul_zero, Algebra.smul_def, map_zero, zero_mul, add_zero]

/-- Restricting to a larger projection replaces the ambient complement by `Q-E`. -/
theorem aeval_idempotent_mul (E Q : R) (hE : E * E = E) (hEQ : E * Q = E)
    (p : 𝕜[X]) :
    aeval E p * Q = p.eval 1 • E + p.eval 0 • (Q - E) := by
  rw [aeval_idempotent E hE, add_mul, smul_mul_assoc, smul_mul_assoc,
    hEQ, sub_mul, one_mul, hEQ]

/-- A projection signal gives one fixed sector and a Chebyshev-zero return sector. -/
theorem chebyshev_idempotent_mul (E Q : R) (hE : E * E = E) (hEQ : E * Q = E)
    (n : ℕ) :
    aeval E (Chebyshev.T 𝕜 (n : ℤ)) * Q =
      E + (Chebyshev.T 𝕜 (n : ℤ)).eval 0 • (Q - E) := by
  rw [aeval_idempotent_mul E Q hE hEQ, Chebyshev.T_eval_one, one_smul]

end GaloisForLFunctions.HilbertMetric.QuantumWalk

#print axioms GaloisForLFunctions.HilbertMetric.QuantumWalk.aeval_idempotent
