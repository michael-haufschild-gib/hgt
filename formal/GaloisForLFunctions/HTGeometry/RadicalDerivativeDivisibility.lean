/-
# The radical divides any cofactor of the derivative

Over a field of characteristic zero, if `N ∣ a · N′` then every prime factor of `N` divides `a`,
hence `radical N ∣ a`.

At a prime `p` of multiplicity `e ≥ 1`, write `N = p^e · N₁` with `p ∤ N₁`.  Then
`N′ = p^{e-1} · (e·p′·N₁ + p·N₁′)`, and the bracket is prime to `p`: `p ∤ e` because the
characteristic is zero, `p ∤ p′` because `p′` is nonzero of smaller degree, and `p ∤ N₁` by
construction.  Cancelling `p^{e-1}` from `p^e · N₁ ∣ a · p^{e-1} · u` leaves `p ∣ a · u`, so `p ∣ a`.

This is the divisibility half of the statement that the reduced denominator of a logarithmic
derivative is the radical.
-/
import Mathlib

noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace GaloisForLFunctions.RadicalDeriv

variable {k : Type*} [Field k] [CharZero k] [DecidableEq k]

omit [CharZero k] [DecidableEq k] in
theorem one_le_degree_of_prime {p : k[X]} (hp : Prime p) : 1 ≤ p.natDegree := by
  by_contra hcon
  have hdeg : p.natDegree = 0 := by omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact hp.ne_zero hc.symm
  exact hp.not_unit (by
    rw [← hc]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))

omit [DecidableEq k] in
theorem not_dvd_derivative_self {p : k[X]} (hp : Prime p) : ¬ p ∣ derivative p := by
  intro hdvd
  have hdeg := one_le_degree_of_prime hp
  have hne : derivative p ≠ 0 := by
    intro h
    have := Polynomial.derivative_eq_zero.mp h
    omega
  have hle : p.degree ≤ (derivative p).degree := Polynomial.degree_le_of_dvd hdvd hne
  have hlt : (derivative p).degree < p.degree := Polynomial.degree_derivative_lt hp.ne_zero
  exact absurd hle (not_le.mpr hlt)

omit [CharZero k] [DecidableEq k] in
theorem not_dvd_C {p : k[X]} (hp : Prime p) {c : k} (hc : c ≠ 0) : ¬ p ∣ Polynomial.C c := by
  intro hdvd
  have hdeg := one_le_degree_of_prime hp
  have hle : p.degree ≤ (Polynomial.C c).degree :=
    Polynomial.degree_le_of_dvd hdvd (by simpa using hc)
  rw [Polynomial.degree_C hc] at hle
  have hpd : (1 : WithBot ℕ) ≤ p.degree := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero]
    exact_mod_cast hdeg
  exact absurd (le_trans hpd hle) (by norm_num)

omit [DecidableEq k] in
/-- **Every prime factor of `N` divides `a` once `N ∣ a · N′`.** -/
theorem prime_dvd_of_dvd_mul_derivative
    {N a p : k[X]} (hN : N ≠ 0) (hp : Prime p) (hpN : p ∣ N)
    (h : N ∣ a * derivative N) : p ∣ a := by
  classical
  have hfin : FiniteMultiplicity p N :=
    FiniteMultiplicity.of_prime_left hp hN
  obtain ⟨N₁, hNeq, hpN₁⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  set e : ℕ := multiplicity p N with he
  have hepos : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · exfalso
      rw [he] at h0
      exact (multiplicity_eq_zero.mp h0) hpN
    · exact hpos
  have hesplit : e = (e - 1) + 1 := by omega
  have hpow : p ^ e = p ^ (e - 1) * p := by
    conv_lhs => rw [hesplit]
    rw [pow_succ]
  set u : k[X] := Polynomial.C ((e : k)) * derivative p * N₁ + p * derivative N₁ with hu
  have hderiv : derivative N = p ^ (e - 1) * u := by
    rw [hNeq, derivative_mul, Polynomial.derivative_pow, hpow, hu]
    ring
  have hpu : ¬ p ∣ u := by
    intro hdvd
    have h1 : p ∣ Polynomial.C ((e : k)) * derivative p * N₁ := by
      have hrw : Polynomial.C ((e : k)) * derivative p * N₁ = u - p * derivative N₁ := by
        rw [hu]; ring
      rw [hrw]
      exact dvd_sub hdvd (Dvd.intro _ rfl)
    rcases hp.dvd_mul.mp h1 with h2 | h2
    · rcases hp.dvd_mul.mp h2 with h3 | h3
      · exact not_dvd_C hp (Nat.cast_ne_zero.mpr (by omega : e ≠ 0)) h3
      · exact not_dvd_derivative_self hp h3
    · exact hpN₁ h2
  rw [hderiv, hNeq, hpow] at h
  have hcancel : p * N₁ ∣ a * u := by
    have hp0 : p ^ (e - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hrw : a * (p ^ (e - 1) * u) = p ^ (e - 1) * (a * u) := by ring
    rw [hrw, mul_assoc] at h
    exact (mul_dvd_mul_iff_left hp0).mp h
  have hpau : p ∣ a * u := dvd_trans (dvd_mul_right p N₁) hcancel
  exact (hp.dvd_mul.mp hpau).resolve_right hpu

/-- **The radical of `N` divides `a` once `N ∣ a · N′`.** -/
theorem radical_dvd_of_dvd_mul_derivative {N a : k[X]} (hN : N ≠ 0) (ha : a ≠ 0)
    (h : N ∣ a * derivative N) : radical N ∣ a := by
  classical
  rw [radical_dvd_iff_primeFactors_subset ha]
  intro q hq
  rw [mem_primeFactors] at hq ⊢
  have hqprime : Prime q := prime_of_normalized_factor q hq
  have hqdvd : q ∣ N := dvd_of_mem_normalizedFactors hq
  have hqnorm : normalize q = q := normalize_normalized_factor q hq
  have hqa : q ∣ a := prime_dvd_of_dvd_mul_derivative hN hqprime hqdvd h
  obtain ⟨q', hq'mem, hassoc⟩ :=
    exists_mem_normalizedFactors_of_dvd ha hqprime.irreducible hqa
  have hqq' : q = q' := by
    have hassoc' : Associated q q' := hassoc
    have h1 : normalize q = normalize q' :=
      normalize_eq_normalize hassoc'.dvd hassoc'.symm.dvd
    rw [hqnorm, normalize_normalized_factor q' hq'mem] at h1
    exact h1
  rw [hqq']
  exact hq'mem

end GaloisForLFunctions.RadicalDeriv

namespace GaloisForLFunctions.RadicalDeriv

open UniqueFactorizationDomain EuclideanDomain

variable {k : Type*} [Field k] [CharZero k] [DecidableEq k]

omit [CharZero k] in
/-- Divisibility by a radical is tested on prime factors. -/
theorem radical_dvd_of_forall_prime {b a : k[X]} (ha : a ≠ 0)
    (h : ∀ p : k[X], Prime p → p ∣ b → p ∣ a) : radical b ∣ a := by
  classical
  rw [radical_dvd_iff_primeFactors_subset ha]
  intro q hq
  rw [mem_primeFactors] at hq ⊢
  have hqprime : Prime q := prime_of_normalized_factor q hq
  have hqdvd : q ∣ b := dvd_of_mem_normalizedFactors hq
  have hqnorm : normalize q = q := normalize_normalized_factor q hq
  obtain ⟨q', hq'mem, hassoc⟩ :=
    exists_mem_normalizedFactors_of_dvd ha hqprime.irreducible (h q hqprime hqdvd)
  have hqq' : q = q' := by
    have hassoc' : Associated q q' := hassoc
    have h1 : normalize q = normalize q' :=
      normalize_eq_normalize hassoc'.dvd hassoc'.symm.dvd
    rw [hqnorm, normalize_normalized_factor q' hq'mem] at h1
    exact h1
  rw [hqq']
  exact hq'mem

omit [CharZero k] in
/-- **The radical of `N·M` clears the logarithmic derivative of `N/M`.** -/
theorem dvd_radical_mul_wronskian {N M : k[X]} (hc : IsCoprime N M) : N * M ∣ radical (N * M) * wronskian N M := by
  have hcop' : IsCoprime (divRadical N) (divRadical M) :=
    (hc.of_isCoprime_of_dvd_left (divRadical_dvd_self N)).of_isCoprime_of_dvd_right
      (divRadical_dvd_self M)
  have hdvd : divRadical (N * M) ∣ wronskian N M := by
    rw [divRadical_mul hc]
    exact hcop'.mul_dvd (divRadical_dvd_wronskian_left N M) (divRadical_dvd_wronskian_right N M)
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_⟩
  rw [ht, ← mul_assoc, radical_mul_divRadical]

/-- **Minimality: any polynomial clearing the logarithmic derivative is a multiple of the
radical.** -/
theorem radical_dvd_of_dvd_mul_wronskian {N M a : k[X]} (hN : N ≠ 0) (hM : M ≠ 0)
    (ha : a ≠ 0) (hc : IsCoprime N M) (h : N * M ∣ a * wronskian N M) :
    radical (N * M) ∣ a := by
  refine radical_dvd_of_forall_prime ha (fun p hp hpNM => ?_)
  rcases hp.dvd_mul.mp hpNM with hpN | hpM
  · have hpM' : ¬ p ∣ M := fun hpM => hp.not_unit (hc.isUnit_of_dvd' hpN hpM)
    have hNdvd : N ∣ a * wronskian N M := dvd_trans (dvd_mul_right N M) h
    have hkey : N ∣ (a * M) * derivative N := by
      have hrw : (a * M) * derivative N = a * (N * derivative M) - a * wronskian N M := by
        rw [wronskian]; ring
      rw [hrw]
      exact dvd_sub ((dvd_mul_right N (derivative M)).mul_left a) hNdvd
    have := prime_dvd_of_dvd_mul_derivative hN hp hpN hkey
    exact (hp.dvd_mul.mp this).resolve_right hpM'
  · have hpN' : ¬ p ∣ N := fun hpN => hp.not_unit (hc.isUnit_of_dvd' hpN hpM)
    have hMdvd : M ∣ a * wronskian N M := dvd_trans (dvd_mul_left M N) h
    have hkey : M ∣ (a * N) * derivative M := by
      have hrw : (a * N) * derivative M = a * wronskian N M + a * (derivative N * M) := by
        rw [wronskian]; ring
      rw [hrw]
      exact dvd_add hMdvd ((dvd_mul_left M (derivative N)).mul_left a)
    have := prime_dvd_of_dvd_mul_derivative hM hp hpM hkey
    exact (hp.dvd_mul.mp this).resolve_right hpN'

/-- **Exact minimal degree.**  The radical of `N·M` is the smallest-degree clearing polynomial. -/
theorem natDegree_radical_le_of_dvd_mul_wronskian {N M a : k[X]} (hN : N ≠ 0) (hM : M ≠ 0)
    (ha : a ≠ 0) (hc : IsCoprime N M) (h : N * M ∣ a * wronskian N M) :
    (radical (N * M)).natDegree ≤ a.natDegree :=
  Polynomial.natDegree_le_of_dvd (radical_dvd_of_dvd_mul_wronskian hN hM ha hc h) ha


end GaloisForLFunctions.RadicalDeriv
