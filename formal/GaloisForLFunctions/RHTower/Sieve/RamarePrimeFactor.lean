import GaloisForLFunctions.RHTower.Sieve.FejerShortInterval
import GaloisForLFunctions.RHTower.Sieve.RamareWeight

/-!
# Ramaré's weight on a coprime factorisation

When `p` is a designated prime not dividing `m`, adjoining it to `m` adds exactly one designated
prime factor:

`primeFactorsIn P (p m) = insert p (primeFactorsIn P m)`,  so  `ω_P(p m) = ω_P(m) + 1`.

That is what makes Ramaré's weight computable on the coprime part of the bilinear decomposition: the
weight `1/ω_P(pm)` becomes `1/(ω_P(m) + 1)`, a function of the cofactor alone.  On the same part a
multiplicative `f` factors, `f(p m) = f(p) f(m)`, so the double sum genuinely becomes bilinear.

The non-coprime part — where `p ∣ m` — is the remainder a sieve bounds separately; it is not
governed by these identities.
-/

namespace RHTower.Sieve

open Finset

/-- **Adjoining a designated prime to a coprime cofactor.** -/
theorem primeFactorsIn_mul_prime {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {p m : ℕ}
    (hp : p.Prime) (hpP : p ∈ P) (hpm : ¬ p ∣ m) :
    primeFactorsIn P (p * m) = insert p (primeFactorsIn P m) := by
  classical
  ext q
  simp only [mem_primeFactorsIn, Finset.mem_insert]
  constructor
  · rintro ⟨hqP, hqdvd⟩
    have hq : q.Prime := hPprime q hqP
    rcases (Nat.Prime.dvd_mul hq).mp hqdvd with hqp | hqm
    · left
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    · right
      exact ⟨hqP, hqm⟩
  · rintro (rfl | ⟨hqP, hqm⟩)
    · exact ⟨hpP, Dvd.intro m rfl⟩
    · exact ⟨hqP, Dvd.dvd.mul_left hqm p⟩

/-- **The Ramaré weight on a coprime factorisation.** -/
theorem card_primeFactorsIn_mul_prime {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {p m : ℕ}
    (hp : p.Prime) (hpP : p ∈ P) (hpm : ¬ p ∣ m) :
    (primeFactorsIn P (p * m)).card = (primeFactorsIn P m).card + 1 := by
  classical
  rw [primeFactorsIn_mul_prime hPprime hp hpP hpm]
  have hnot : p ∉ primeFactorsIn P m := by
    rw [mem_primeFactorsIn]
    intro hcon
    exact hpm hcon.2
  rw [Finset.card_insert_of_notMem hnot]

/-- **A multiplicative function factors on a coprime factorisation.** -/
theorem map_mul_prime_of_not_dvd {f : ℕ → ℝ}
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) {p m : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) :
    f (p * m) = f p * f m :=
  hmul p m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)

end RHTower.Sieve
