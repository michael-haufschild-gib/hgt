import GaloisForLFunctions.RHTower.Sieve.DampedEulerSeriesBound
import GaloisForLFunctions.RHTower.VonMangoldtThreeFourOneSeries

/-!
# The prime term of the damped series in cosine form

The Euler bound's exponent is a sum over primes of `Re(f(p)p^{-s})`.  For the damped Möbius function
that term is `−(if p ∈ P then t else 1)·p^{-σ}·cos(τ log p)`, which is exactly the negative of the
summand of `RHTower.dampedCosPlusSum` at `σ = 1`, shifted by `p^{-σ}`.

Writing it out is what connects the series bound to the pretentious distance.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The designated prime count of a prime. -/
theorem card_primeFactorsIn_prime {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {p : ℕ}
    (hp : p.Prime) :
    (primeFactorsIn P p).card = if p ∈ P then 1 else 0 := by
  classical
  by_cases hmem : p ∈ P
  · rw [if_pos hmem]
    have hset : primeFactorsIn P p = {p} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨mem_primeFactorsIn.2 ⟨hmem, dvd_rfl⟩, ?_⟩
      intro q hq
      rw [mem_primeFactorsIn] at hq
      exact ((Nat.prime_dvd_prime_iff_eq (hPprime q hq.1) hp).1 hq.2)
    rw [hset, Finset.card_singleton]
  · rw [if_neg hmem]
    have hset : primeFactorsIn P p = ∅ := by
      rw [primeFactorsIn, Finset.filter_eq_empty_iff]
      intro q hq hdvd
      have : q = p := (Nat.prime_dvd_prime_iff_eq (hPprime q hq) hp).1 hdvd
      exact hmem (this ▸ hq)
    rw [hset, Finset.card_empty]

/-- **The prime term of the damped series, in cosine form.** -/
theorem twistedSummand_dampedOmegaMoebius_prime_re {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {p : ℕ} (hp : p.Prime) (t σ τ : ℝ) :
    (twistedSummand (dampedOmegaMoebius P t) ((σ : ℂ) + (τ : ℂ) * Complex.I) p).re
      = -((if p ∈ P then t else 1) * ((p : ℝ) ^ (-σ) * Real.cos (τ * Real.log p))) := by
  have hp0 : 0 < p := hp.pos
  have hmu : ((moebius p : ℤ) : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  have hcard := card_primeFactorsIn_prime hPprime hp
  have hcoeff : dampedOmegaMoebius P t p = -(((if p ∈ P then t else 1 : ℝ)) : ℂ) := by
    rw [dampedOmegaMoebius, hmu, hcard]
    by_cases hmem : p ∈ P
    · rw [if_pos hmem, if_pos hmem, pow_one]
      ring
    · rw [if_neg hmem, if_neg hmem, pow_zero]
      push_cast
      ring
  rw [twistedSummand, hcoeff, ← Complex.ofReal_neg, Complex.re_ofReal_mul,
    re_natCast_cpow_neg hp0 σ τ]
  ring

end

end RHTower.Sieve
