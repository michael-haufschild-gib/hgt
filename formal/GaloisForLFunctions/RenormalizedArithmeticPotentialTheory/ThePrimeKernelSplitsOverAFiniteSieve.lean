import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHasOneEulerConstant
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsHeckeCovariant

/-!
# The prime kernel splits over a finite sieve

Every positive integer has a part supported on a finite prime set and a coprime
part. A prime-power quotient changes just one of these factors. Consequently
Weil's prime kernel is an exact tensor sum before imposing the horizon cutoff.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticIntersectionTheory
  ArithmeticFunction

/-- An integer whose prime divisors all lie in the finite sieve. -/
def SieveSupported (Q : Finset Nat.Primes) (d : ℕ) : Prop :=
  ∃ r : ℕ, d ∣ sievePrimorial Q ^ r

theorem SieveSupported.pos {Q : Finset Nat.Primes} {d : ℕ}
    (hd : SieveSupported Q d) : 0 < d := by
  obtain ⟨r, hr⟩ := hd
  exact Nat.pos_of_dvd_of_pos hr (pow_pos (Nat.pos_of_ne_zero (sievePrimorial_ne_zero Q)) r)

theorem SieveSupported.mul {Q : Finset Nat.Primes} {d e : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) : SieveSupported Q (d * e) := by
  obtain ⟨r, hr⟩ := hd
  obtain ⟨s, hs⟩ := he
  exact ⟨r + s, by rw [pow_add]; exact mul_dvd_mul hr hs⟩

theorem SieveSupported.coprime {Q : Finset Nat.Primes} {d k : ℕ}
    (hd : SieveSupported Q d) (hk : Nat.Coprime k (sievePrimorial Q)) :
    Nat.Coprime d k := by
  obtain ⟨r, hr⟩ := hd
  exact Nat.Coprime.coprime_dvd_left hr (hk.symm.pow_left r)

/-- The supported and coprime factors are uniquely determined by their product. -/
theorem sieveFactorization_unique {Q : Finset Nat.Primes} {d e k l : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e)
    (hk : Nat.Coprime k (sievePrimorial Q)) (hl : Nat.Coprime l (sievePrimorial Q))
    (h : d * k = e * l) : d = e ∧ k = l := by
  have hde : d ∣ e := (hd.coprime hl).dvd_of_dvd_mul_right
    (by rw [← h]; exact dvd_mul_right d k)
  have hed : e ∣ d := (he.coprime hk).dvd_of_dvd_mul_right
    (by rw [h]; exact dvd_mul_right e l)
  have hde' := Nat.dvd_antisymm hde hed
  refine ⟨hde', ?_⟩
  rw [← hde'] at h
  exact Nat.eq_of_mul_eq_mul_left hd.pos h

/-- A nonzero prime-power interaction changes at most one sieve factor. -/
theorem sieveFactors_eq_or_eq_of_vonMangoldt_ne_zero
    {Q : Finset Nat.Primes} {d e k l : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e)
    (hk : Nat.Coprime k (sievePrimorial Q)) (hl : Nat.Coprime l (sievePrimorial Q))
    (hdiv : d * k ∣ e * l) (hΛ : Λ (e * l / (d * k)) ≠ 0) : d = e ∨ k = l := by
  obtain ⟨p, r, hp, _, hpow⟩ :=
    (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  have hmul : (d * k) * p ^ r = e * l := by
    rw [hpow]
    exact Nat.mul_div_cancel' hdiv
  by_cases hpQ : p ∣ sievePrimorial Q
  · right
    have hsup : SieveSupported Q (p ^ r) := ⟨r, pow_dvd_pow_of_dvd hpQ r⟩
    have hprod : (d * p ^ r) * k = e * l := by
      calc (d * p ^ r) * k = (d * k) * p ^ r := by ac_rfl
           _ = e * l := hmul
    exact (sieveFactorization_unique (hd.mul hsup) he hk hl hprod).2
  · left
    have hcop : Nat.Coprime (k * p ^ r) (sievePrimorial Q) :=
      hk.mul_left ((hp.coprime_iff_not_dvd.mpr hpQ).pow_left r)
    have hprod : d * (k * p ^ r) = e * l := by rw [← mul_assoc]; exact hmul
    exact (sieveFactorization_unique hd he hcop hl hprod).1

/-- Different supported factors and different coprime factors have zero coupling. -/
theorem weilPrimeKernel_sieveFactors_eq_zero
    {Q : Finset Nat.Primes} {d e k l : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e)
    (hk : Nat.Coprime k (sievePrimorial Q)) (hl : Nat.Coprime l (sievePrimorial Q))
    (hde : d ≠ e) (hkl : k ≠ l) : weilPrimeKernel (d * k) (e * l) = 0 := by
  unfold weilPrimeKernel
  split_ifs with hforward hreverse
  · have hzero : Λ (e * l / (d * k)) = 0 := by
      by_contra hΛ
      exact (sieveFactors_eq_or_eq_of_vonMangoldt_ne_zero hd he hk hl hforward.1 hΛ).elim hde hkl
    rw [hzero, zero_div]
  · have hzero : Λ (d * k / (e * l)) = 0 := by
      by_contra hΛ
      exact (sieveFactors_eq_or_eq_of_vonMangoldt_ne_zero he hd hl hk hreverse.1 hΛ).elim
        (Ne.symm hde) (Ne.symm hkl)
    rw [hzero, zero_div]
  · rfl

/-- Exact tensor sum of the supported-prime kernel and the complementary kernel. -/
theorem weilPrimeKernel_sieve_tensor_sum
    {Q : Finset Nat.Primes} {d e k l : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e)
    (hk : Nat.Coprime k (sievePrimorial Q)) (hl : Nat.Coprime l (sievePrimorial Q))
    (hk0 : 0 < k) :
    weilPrimeKernel (d * k) (e * l) =
      (if d = e then weilPrimeKernel k l else 0) +
        (if k = l then weilPrimeKernel d e else 0) := by
  by_cases hde : d = e
  · subst e
    rw [if_pos rfl, weilPrimeKernel_mul_left hd.pos, weilPrimeKernel_self]
    simp
  · by_cases hkl : k = l
    · subst l
      rw [if_neg hde, if_pos rfl, zero_add]
      simpa only [mul_comm] using weilPrimeKernel_mul_left hk0 d e
    · rw [if_neg hde, if_neg hkl, add_zero]
      exact weilPrimeKernel_sieveFactors_eq_zero hd he hk hl hde hkl

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
