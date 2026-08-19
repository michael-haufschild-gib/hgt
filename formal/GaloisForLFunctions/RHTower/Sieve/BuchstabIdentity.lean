import Mathlib

/-!
# Buchstab's identity

`rho n z` is the indicator of "`n` is positive and has no prime factor below `z`", that is
`1_{(n, P(z)) = 1}` for the primorial `P(z) = ∏_{p<z} p`.  Buchstab's identity says that lowering
the sifting level from `z` to `w` adds exactly the integers whose least prime factor lies in
`[w, z)`, each recorded through its cofactor:

```text
        rho n z + ∑_{q prime, q ∣ n, w ≤ q < z} rho (n/q) q = rho n w .
```

The sum has at most one nonzero term — the least prime factor of `n`, when it lies in the window.
-/

namespace RHTower.Sieve

open Finset

/-- The sifting indicator: `rho n z = 1` exactly when `n` is positive and has no prime factor
below `z`. -/
def rho (n z : ℕ) : ℕ := if 0 < n ∧ ∀ p ∈ n.primeFactors, z ≤ p then 1 else 0

theorem rho_le_one (n z : ℕ) : rho n z ≤ 1 := by
  rw [rho]; split <;> omega

theorem rho_eq_one_iff {n z : ℕ} :
    rho n z = 1 ↔ (0 < n ∧ ∀ p ∈ n.primeFactors, z ≤ p) := by
  rw [rho]; split <;> simp_all

theorem rho_eq_zero_iff {n z : ℕ} :
    rho n z = 0 ↔ ¬ (0 < n ∧ ∀ p ∈ n.primeFactors, z ≤ p) := by
  rw [rho]; split <;> simp_all

theorem rho_eq_zero_of_lt {n z p : ℕ} (hp : p ∈ n.primeFactors) (hlt : p < z) : rho n z = 0 := by
  rw [rho_eq_zero_iff]
  rintro ⟨-, hall⟩
  exact absurd (hall p hp) (by omega)

theorem rho_eq_one_of {n z : ℕ} (hn : 0 < n) (hall : ∀ p ∈ n.primeFactors, z ≤ p) :
    rho n z = 1 := rho_eq_one_iff.2 ⟨hn, hall⟩

/-- Raising the sifting level can only remove integers. -/
theorem rho_antitone {n w z : ℕ} (hwz : w ≤ z) : rho n z ≤ rho n w := by
  rcases Nat.eq_zero_or_pos (rho n z) with h | h
  · omega
  · have h1 : rho n z = 1 := by have := rho_le_one n z; omega
    have h2 := rho_eq_one_iff.1 h1
    have h3 : rho n w = 1 := rho_eq_one_of h2.1 fun p hp => le_trans hwz (h2.2 p hp)
    omega

/-- A prime factor other than `q` survives division by `q`. -/
theorem dvd_div_of_ne {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n)
    (hne : p ≠ q) : p ∣ n / q := by
  obtain ⟨m, hm⟩ := hqn
  have hq0 : 0 < q := hq.pos
  have hdiv : n / q = m := by rw [hm, Nat.mul_div_cancel_left _ hq0]
  rw [hdiv]
  rw [hm] at hpn
  rcases (Nat.Prime.dvd_mul hp).1 hpn with hcase | hcase
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).1 hcase) hne
  · exact hcase

/-- **Buchstab's identity.** -/
theorem buchstab {n w z : ℕ} (hn : 0 < n) (hwz : w ≤ z) :
    rho n z + ∑ q ∈ (Finset.Ico w z).filter (fun q => q.Prime ∧ q ∣ n), rho (n / q) q
      = rho n w := by
  classical
  -- a prime factor below `w` kills every term
  have hkill : ∀ p, p ∈ n.primeFactors → p < w →
      (rho n z = 0 ∧ ∀ q ∈ (Finset.Ico w z).filter (fun q => q.Prime ∧ q ∣ n),
        rho (n / q) q = 0) := by
    intro p hp hpw
    refine ⟨rho_eq_zero_of_lt hp (by omega), fun q hq => ?_⟩
    rw [Finset.mem_filter, Finset.mem_Ico] at hq
    obtain ⟨⟨hwq, -⟩, hqp, hqn⟩ := hq
    have hpprime : p.Prime := (Nat.mem_primeFactors.1 hp).1
    have hpn : p ∣ n := (Nat.mem_primeFactors.1 hp).2.1
    have hne : p ≠ q := by omega
    have hdvd : p ∣ n / q := dvd_div_of_ne hpprime hqp hpn hqn hne
    have hq0 : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqn) hqp.pos
    refine rho_eq_zero_of_lt (p := p) ?_ (by omega)
    exact Nat.mem_primeFactors.2 ⟨hpprime, hdvd, by omega⟩
  by_cases hw : ∀ p ∈ n.primeFactors, w ≤ p
  · -- `n` is already `w`-rough
    have hrw : rho n w = 1 := rho_eq_one_of hn hw
    by_cases hz : ∀ p ∈ n.primeFactors, z ≤ p
    · -- nothing to add: the window contains no prime factor
      have hrz : rho n z = 1 := rho_eq_one_of hn hz
      have hempty : (Finset.Ico w z).filter (fun q => q.Prime ∧ q ∣ n) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
        rw [Finset.mem_filter, Finset.mem_Ico] at hq
        obtain ⟨⟨-, hqz⟩, hqp, hqn⟩ := hq
        have : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hqp, hqn, by omega⟩
        exact absurd (hz q this) (by omega)
      rw [hrz, hempty, Finset.sum_empty, hrw]
      omega
    · -- the least prime factor lies in the window
      obtain ⟨p, hp, hpz⟩ : ∃ p ∈ n.primeFactors, p < z := by
        by_contra hcon
        exact hz fun p hp => by
          by_contra hlt
          exact hcon ⟨p, hp, by omega⟩
      have hrz : rho n z = 0 := rho_eq_zero_of_lt hp hpz
      have hn1 : 1 < n := by
        rcases Nat.lt_or_ge 1 n with h | h
        · exact h
        · exfalso
          have hone : n = 1 := by omega
          rw [hone] at hp
          simp at hp
      set p₀ : ℕ := n.minFac with hp₀
      have hp₀p : p₀.Prime := Nat.minFac_prime (by omega)
      have hp₀n : p₀ ∣ n := Nat.minFac_dvd n
      have hp₀mem : p₀ ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp₀p, hp₀n, by omega⟩
      have hp₀le : ∀ q ∈ n.primeFactors, p₀ ≤ q := fun q hq =>
        Nat.minFac_le_of_dvd (Nat.mem_primeFactors.1 hq).1.two_le
          (Nat.mem_primeFactors.1 hq).2.1
      have hp₀z : p₀ < z := lt_of_le_of_lt (hp₀le p hp) hpz
      have hp₀w : w ≤ p₀ := hw p₀ hp₀mem
      have hmem : p₀ ∈ (Finset.Ico w z).filter (fun q => q.Prime ∧ q ∣ n) := by
        rw [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨hp₀w, hp₀z⟩, hp₀p, hp₀n⟩
      have hone : rho (n / p₀) p₀ = 1 := by
        refine rho_eq_one_of (Nat.div_pos (Nat.le_of_dvd (by omega) hp₀n) hp₀p.pos) ?_
        intro r hr
        have hrp : r.Prime := (Nat.mem_primeFactors.1 hr).1
        have hrd : r ∣ n / p₀ := (Nat.mem_primeFactors.1 hr).2.1
        have hrn : r ∣ n := hrd.trans (Nat.div_dvd_of_dvd hp₀n)
        exact hp₀le r (Nat.mem_primeFactors.2 ⟨hrp, hrn, by omega⟩)
      have hsum : ∑ q ∈ (Finset.Ico w z).filter (fun q => q.Prime ∧ q ∣ n), rho (n / q) q = 1 := by
        rw [Finset.sum_eq_single_of_mem p₀ hmem ?_, hone]
        intro q hq hne
        rw [Finset.mem_filter, Finset.mem_Ico] at hq
        obtain ⟨⟨hwq, hqz⟩, hqp, hqn⟩ := hq
        have hqmem : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hqp, hqn, by omega⟩
        have hlt : p₀ < q := lt_of_le_of_ne (hp₀le q hqmem) (Ne.symm hne)
        have hdvd : p₀ ∣ n / q := dvd_div_of_ne hp₀p hqp hp₀n hqn (by omega)
        have hq0 : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqn) hqp.pos
        exact rho_eq_zero_of_lt (p := p₀) (Nat.mem_primeFactors.2 ⟨hp₀p, hdvd, by omega⟩) hlt
      rw [hrz, hsum, hrw]
  · -- `n` has a prime factor below `w`
    obtain ⟨p, hp, hpw⟩ : ∃ p ∈ n.primeFactors, p < w := by
      by_contra hcon
      exact hw fun p hp => by
        by_contra hlt
        exact hcon ⟨p, hp, by omega⟩
    obtain ⟨hrz, hterms⟩ := hkill p hp hpw
    rw [hrz, Finset.sum_congr rfl hterms, Finset.sum_const_zero,
      rho_eq_zero_of_lt hp hpw]
    omega

end RHTower.Sieve
