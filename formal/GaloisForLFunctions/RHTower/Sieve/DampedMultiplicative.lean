import GaloisForLFunctions.RHTower.Sieve.DampedCofactorIntegral
import GaloisForLFunctions.RHTower.Sieve.RamarePrimeFactor

/-!
# The damped Möbius function is multiplicative

`μ(m)·t^{ω_P(m)}` is multiplicative on coprime arguments, because the designated prime count is
additive there: a prime of `P` divides `mn` exactly when it divides one of the factors, and
coprimality forbids both.

Multiplicativity together with the unit bound is what lets the Euler bound
`Sieve/MultiplicativeEulerBound.norm_tsum_twistedSummand_le_exp` be applied to the damped series, and
that bound is the bridge from the pretentious distance to a bound on the Dirichlet series.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The designated prime factors split over any factorisation.** -/
theorem primeFactorsIn_mul {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (m n : ℕ) :
    primeFactorsIn P (m * n) = primeFactorsIn P m ∪ primeFactorsIn P n := by
  classical
  rw [primeFactorsIn, primeFactorsIn, primeFactorsIn, ← Finset.filter_or]
  refine Finset.filter_congr ?_
  intro p hp
  exact (Nat.Prime.dvd_mul (hPprime p hp)).symm.symm

/-- The two factor sets are disjoint. -/
theorem primeFactorsIn_disjoint_of_coprime {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {m n : ℕ}
    (h : Nat.Coprime m n) :
    Disjoint (primeFactorsIn P m) (primeFactorsIn P n) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpm hpn
  rw [mem_primeFactorsIn] at hpm hpn
  have hp : p.Prime := hPprime p hpm.1
  have hdvd : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm.2 hpn.2
  have hg : Nat.gcd m n = 1 := h
  rw [hg] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)

/-- **The designated prime count is additive on coprime factorisations.** -/
theorem card_primeFactorsIn_mul_of_coprime {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {m n : ℕ}
    (h : Nat.Coprime m n) :
    (primeFactorsIn P (m * n)).card
      = (primeFactorsIn P m).card + (primeFactorsIn P n).card := by
  rw [primeFactorsIn_mul hPprime m n,
    Finset.card_union_of_disjoint (primeFactorsIn_disjoint_of_coprime hPprime h)]

/-- **The damped Möbius function is multiplicative.** -/
theorem dampedOmegaMoebius_mul_of_coprime {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (t : ℝ)
    {m n : ℕ} (h : Nat.Coprime m n) :
    dampedOmegaMoebius P t (m * n)
      = dampedOmegaMoebius P t m * dampedOmegaMoebius P t n := by
  rw [dampedOmegaMoebius, dampedOmegaMoebius, dampedOmegaMoebius,
    card_primeFactorsIn_mul_of_coprime hPprime h,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, pow_add]
  push_cast
  ring

/-- The damped function at one. -/
theorem dampedOmegaMoebius_one {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (t : ℝ) :
    dampedOmegaMoebius P t 1 = 1 := by
  classical
  have hone : primeFactorsIn P 1 = ∅ := by
    rw [primeFactorsIn, Finset.filter_eq_empty_iff]
    intro p hp hdvd
    exact absurd (Nat.dvd_one.mp hdvd) (hPprime p hp).one_lt.ne'
  rw [dampedOmegaMoebius, hone]
  simp

end

end RHTower.Sieve
