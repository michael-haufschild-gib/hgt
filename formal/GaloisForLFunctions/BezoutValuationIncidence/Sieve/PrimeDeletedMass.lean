import GaloisForLFunctions.RHTower.Sieve.IntervalSelberg
import GaloisForLFunctions.RHTower.Sieve.CoprimeSquarefreeHarmonic

/-!
# Logarithmic sieve mass after deleting one prime

Squarefree integers coprime to twice the deleted prime retain a fixed fraction
of the harmonic mass. They divide the remaining primorial, uniformly in the
deleted prime and the sieve level.
-/

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

open Finset Nat
open _root_.RHTower.Sieve

/-- The product of primes up to the sieve level, except one specified prime. -/
def primeDeletedPrimorial (p Y : ℕ) : ℕ :=
  ∏ q ∈ (Nat.primesLE Y).filter (fun q => q ≠ p), q

/-- Deleting a prime from the primorial preserves squarefreeness. -/
theorem primeDeletedPrimorial_squarefree (p Y : ℕ) : Squarefree (primeDeletedPrimorial p Y) := by
  apply (squarefree_primorial Y).squarefree_of_dvd
  rw [primorial_eq_prod_primesLE]
  exact prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)

/-- The deleted prime is coprime to the remaining prime product. -/
theorem primeDeletedPrimorial_coprime {p : ℕ} (hp : p.Prime) (Y : ℕ) :
    p.Coprime (primeDeletedPrimorial p Y) := by
  apply Nat.Coprime.prod_right
  intro q hq
  obtain ⟨hqY, hqp⟩ := mem_filter.mp hq
  exact (Nat.coprime_primes hp (Nat.mem_primesLE.mp hqY).2).mpr hqp.symm

/-- Every small squarefree integer avoiding the deleted prime divides the sieve modulus. -/
theorem squarefree_dvd_primeDeletedPrimorial {p Y d : ℕ}
    (hd : Squarefree d) (hdY : d ≤ Y) (hpd : p.Coprime d) :
    d ∣ primeDeletedPrimorial p Y := by
  have hsub : d.primeFactors ⊆ (Nat.primesLE Y).filter (fun q => q ≠ p) := by
    intro q hq
    have hqP := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    refine mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero) hqd).trans hdY, hqP⟩, ?_⟩
    intro hqp
    subst q
    exact (hqP.coprime_iff_not_dvd.mp hpd) hqd
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact prod_dvd_prod_of_subset _ _ _ hsub

/-- Excluding two and a prime at least eight removes reciprocal prime mass at most five eighths. -/
theorem prime_pair_reciprocals_le {p : ℕ} (hp : p.Prime) (hp8 : 8 ≤ p) :
    ∑ q ∈ (2 * p).primeFactors, 1 / (q : ℝ) ≤ 5 / 8 := by
  have h2p : 2 ≠ p := by omega
  rw [Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0) hp.ne_zero,
    Nat.prime_two.primeFactors, hp.primeFactors, singleton_union,
    sum_insert (by simpa only [mem_singleton] using h2p), sum_singleton]
  have hpR : (8 : ℝ) ≤ p := by exact_mod_cast hp8
  have hi : 1 / (p : ℝ) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hpR
  norm_num only [Nat.cast_ofNat]
  linarith only [hi]

/-- The reciprocal divisor mass stays logarithmic after deleting one large prime. -/
theorem primeDeletedPrimorial_reciprocal_mass_lower {p Y : ℕ} (hp : p.Prime) (hp8 : 8 ≤ p) (hY : 1 ≤ Y) :
    (1 / 8 : ℝ) * Real.log Y - 7 / 8 ≤
      ∑ d ∈ (primeDeletedPrimorial p Y).divisors.filter (fun d => d ≤ Y), 1 / (d : ℝ) := by
  have hmass := sum_inv_coprime_squarefree_ge
    (Nat.mul_ne_zero (by norm_num : (2 : ℕ) ≠ 0) hp.ne_zero)
    (dvd_mul_right 2 p) hY (prime_pair_reciprocals_le hp hp8)
  refine hmass.trans ?_
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hdY, hdcop, hdsq⟩ := mem_filter.mp hd
    have hpd : p.Coprime d := (Nat.Coprime.of_dvd_right (dvd_mul_left p 2) hdcop).symm
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨squarefree_dvd_primeDeletedPrimorial hdsq (mem_Icc.mp hdY).2 hpd,
        (primeDeletedPrimorial_squarefree p Y).ne_zero⟩, (mem_Icc.mp hdY).2⟩
  · intro d _ _
    positivity

#print axioms primeDeletedPrimorial_reciprocal_mass_lower

end GaloisForLFunctions.BezoutValuationIncidence
