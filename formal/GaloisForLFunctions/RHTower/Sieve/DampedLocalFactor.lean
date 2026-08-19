import GaloisForLFunctions.RHTower.Sieve.DampedPrimeTerm
import GaloisForLFunctions.RHTower.Sieve.DampedEulerCorrection

/-!
# The local Euler factor of the damped Möbius series

The damped Möbius function vanishes at every prime power `p^k` with `k ≥ 2`, because `μ` does, so
its local factor has only two terms:

`∑_k f(p^k) p^{-ks} = 1 − (if p ∈ P then t else 1)·p^{-s}`.

Off `P` that is the local factor of `1/ζ`, and on `P` it is that factor times
`Sieve/DampedEulerCorrection.dampedEulerFactor`.  This is the arithmetic content of the Euler
identity `∑'_m μ(m)t^{ω_P(m)}m^{-s} = (1/ζ(s))·∏_{p ∈ P} dampedEulerFactor t p s`; what remains of
that identity is infinite-product plumbing.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The damped coefficient at a prime. -/
theorem dampedOmegaMoebius_prime {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (t : ℝ) {p : ℕ}
    (hp : p.Prime) :
    dampedOmegaMoebius P t p = -(((if p ∈ P then t else 1 : ℝ)) : ℂ) := by
  have hmu : ((moebius p : ℤ) : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  rw [dampedOmegaMoebius, hmu, card_primeFactorsIn_prime hPprime hp]
  by_cases hmem : p ∈ P
  · rw [if_pos hmem, if_pos hmem, pow_one]
    ring
  · rw [if_neg hmem, if_neg hmem, pow_zero]
    push_cast
    ring

/-- The damped coefficient vanishes at higher prime powers. -/
theorem dampedOmegaMoebius_primePow_eq_zero (P : Finset ℕ) (t : ℝ) {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) : dampedOmegaMoebius P t (p ^ k) = 0 := by
  have hsq : ¬ Squarefree (p ^ k) := by
    intro hsf
    have hdvd : p * p ∣ p ^ k := by
      have : p ^ 2 ∣ p ^ k := pow_dvd_pow p hk
      rwa [pow_two] at this
    exact absurd (Nat.isUnit_iff.1 (hsf p hdvd)) hp.ne_one
  rw [dampedOmegaMoebius, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  push_cast
  ring

/-- **The local Euler factor of the damped series.** -/
theorem tsum_twistedSummand_dampedOmegaMoebius_primePow {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (t : ℝ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ∑' k : ℕ, twistedSummand (dampedOmegaMoebius P t) s (p ^ k)
      = 1 - (((if p ∈ P then t else 1 : ℝ)) : ℂ) * (p : ℂ) ^ (-s) := by
  classical
  have hzero : ∀ k ∉ ({0, 1} : Finset ℕ),
      twistedSummand (dampedOmegaMoebius P t) s (p ^ k) = 0 := by
    intro k hk
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      omega
    rw [twistedSummand, dampedOmegaMoebius_primePow_eq_zero P t hp hk2, zero_mul]
  rw [tsum_eq_sum hzero]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  have h0 : twistedSummand (dampedOmegaMoebius P t) s (p ^ 0) = 1 := by
    rw [pow_zero, twistedSummand, dampedOmegaMoebius_one hPprime t, Nat.cast_one,
      Complex.one_cpow, mul_one]
  have h1 : twistedSummand (dampedOmegaMoebius P t) s (p ^ 1)
      = -((((if p ∈ P then t else 1 : ℝ)) : ℂ) * (p : ℂ) ^ (-s)) := by
    rw [pow_one, twistedSummand, dampedOmegaMoebius_prime hPprime t hp]
    ring
  rw [h0, h1]
  ring

end

end RHTower.Sieve
