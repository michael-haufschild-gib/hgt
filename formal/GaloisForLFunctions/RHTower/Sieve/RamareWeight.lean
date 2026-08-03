import GaloisForLFunctions.RHTower.Sieve.SharedPrimeTail

/-!
# Ramaré's weighted factorization identity

Every integer carrying at least one prime factor from a designated set `P` can be split over those
factors with total weight one: writing `ω_P(n)` for the number of primes of `P` dividing `n`,

`∑_{p ∈ P, p ∣ n} 1 / ω_P(n) = 1`.

Summing that over a finite set `S` and exchanging the two sums turns *any* sum over `S` into a sum
over pairs `(p, m)` with `p ∈ P` and `n = p m`:

`∑_{n ∈ S} f(n) = ∑_{p ∈ P} ∑_{m} f(p m) / ω_P(p m)`.

The identity is exact — no error term and no hypothesis beyond `ω_P(n) ≠ 0` — and it is the device
that manufactures a bilinear structure out of a one-dimensional sum.  The weight `1/ω_P` is what
prevents an integer with several factors in `P` from being counted several times.
-/

namespace RHTower.Sieve

open Finset

/-- The members of a designated set dividing `n`. -/
def primeFactorsIn (P : Finset ℕ) (n : ℕ) : Finset ℕ := {p ∈ P | p ∣ n}

theorem mem_primeFactorsIn {P : Finset ℕ} {n p : ℕ} :
    p ∈ primeFactorsIn P n ↔ p ∈ P ∧ p ∣ n := by
  rw [primeFactorsIn, Finset.mem_filter]

/-- **Ramaré's identity.**  Splitting an integer over its designated prime factors has total
weight one. -/
theorem sum_inv_card_primeFactorsIn {P : Finset ℕ} {n : ℕ}
    (hn : (primeFactorsIn P n).Nonempty) :
    ∑ _p ∈ primeFactorsIn P n, (1 : ℝ) / ((primeFactorsIn P n).card : ℝ) = 1 := by
  have hcard : 0 < (primeFactorsIn P n).card := Finset.card_pos.2 hn
  have hcardR : (0 : ℝ) < ((primeFactorsIn P n).card : ℝ) := by exact_mod_cast hcard
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- **Weighted factorization.**  Any sum over a set of integers, each carrying a designated prime
factor, is the double sum over designated primes and their multiples. -/
theorem sum_eq_sum_ramare (P S : Finset ℕ) (f : ℕ → ℝ)
    (hS : ∀ n ∈ S, (primeFactorsIn P n).Nonempty) :
    ∑ n ∈ S, f n
      = ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, f n / ((primeFactorsIn P n).card : ℝ) := by
  classical
  have hswap : ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, f n / ((primeFactorsIn P n).card : ℝ)
      = ∑ p ∈ P, ∑ n ∈ S, (if p ∣ n then f n / ((primeFactorsIn P n).card : ℝ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.sum_filter]
  rw [hswap, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hne : (primeFactorsIn P n).Nonempty := hS n hn
  have hcard : 0 < (primeFactorsIn P n).card := Finset.card_pos.2 hne
  have hcardR : (0 : ℝ) < ((primeFactorsIn P n).card : ℝ) := by exact_mod_cast hcard
  rw [← Finset.sum_filter]
  have hfilter : {p ∈ P | p ∣ n} = primeFactorsIn P n := rfl
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Reindexing a sum over multiples of `p` by the cofactor. -/
theorem sum_div_image (p : ℕ) (T : Finset ℕ) (hT : ∀ n ∈ T, p ∣ n) (g : ℕ → ℝ) :
    ∑ m ∈ T.image (fun n => n / p), g (p * m) = ∑ n ∈ T, g n := by
  classical
  have hinj : ∀ x ∈ T, ∀ y ∈ T, x / p = y / p → x = y := by
    intro x hx y hy hxy
    have h1 : p * (x / p) = x := Nat.mul_div_cancel' (hT x hx)
    have h2 : p * (y / p) = y := Nat.mul_div_cancel' (hT y hy)
    rw [← h1, ← h2, hxy]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [Nat.mul_div_cancel' (hT n hn)]

/-- **Bilinear form of Ramaré's identity.**  The sum becomes one over designated primes and their
cofactors. -/
theorem sum_eq_sum_ramare_bilinear (P S : Finset ℕ) (f : ℕ → ℝ)
    (hS : ∀ n ∈ S, (primeFactorsIn P n).Nonempty) :
    ∑ n ∈ S, f n
      = ∑ p ∈ P, ∑ m ∈ ({n ∈ S | p ∣ n}).image (fun n => n / p),
          f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ) := by
  classical
  rw [sum_eq_sum_ramare P S f hS]
  refine Finset.sum_congr rfl ?_
  intro p _
  refine (sum_div_image p _ ?_ _).symm
  intro n hn
  exact (Finset.mem_filter.1 hn).2

/-- **Complete Ramaré decomposition.**  Every sum splits into its weighted bilinear part and the
part carried by integers with no designated prime factor at all — the rough remainder, which the
sieve bounds separately. -/
theorem sum_eq_ramare_add_rough (P S : Finset ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ S, f n
      = (∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, f n / ((primeFactorsIn P n).card : ℝ))
        + ∑ n ∈ {n ∈ S | primeFactorsIn P n = ∅}, f n := by
  classical
  set S' : Finset ℕ := {n ∈ S | (primeFactorsIn P n).Nonempty} with hS'
  have hsplit : ∑ n ∈ S, f n
      = ∑ n ∈ S', f n + ∑ n ∈ {n ∈ S | ¬ (primeFactorsIn P n).Nonempty}, f n := by
    rw [hS']
    exact (Finset.sum_filter_add_sum_filter_not S (fun n => (primeFactorsIn P n).Nonempty) f).symm
  have hrough : {n ∈ S | ¬ (primeFactorsIn P n).Nonempty} = {n ∈ S | primeFactorsIn P n = ∅} := by
    refine Finset.filter_congr ?_
    intro n _
    rw [Finset.not_nonempty_iff_eq_empty]
  have hmain : ∑ n ∈ S', f n
      = ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, f n / ((primeFactorsIn P n).card : ℝ) := by
    have hne : ∀ n ∈ S', (primeFactorsIn P n).Nonempty := by
      intro n hn
      exact (Finset.mem_filter.1 hn).2
    rw [sum_eq_sum_ramare P S' f hne]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hsets : {n ∈ S' | p ∣ n} = {n ∈ S | p ∣ n} := by
      ext n
      simp only [hS', Finset.mem_filter]
      constructor
      · rintro ⟨⟨hnS, -⟩, hpn⟩
        exact ⟨hnS, hpn⟩
      · rintro ⟨hnS, hpn⟩
        exact ⟨⟨hnS, ⟨p, mem_primeFactorsIn.2 ⟨hp, hpn⟩⟩⟩, hpn⟩
    rw [hsets]
  rw [hsplit, hrough, hmain]

end RHTower.Sieve
