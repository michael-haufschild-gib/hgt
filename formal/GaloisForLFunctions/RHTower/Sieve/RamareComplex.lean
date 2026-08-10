import GaloisForLFunctions.RHTower.Sieve.RamareWeight
import GaloisForLFunctions.RHTower.Sieve.GallagherLemma

/-!
# Ramaré's weighted factorization for a complex weight

The corpus's Ramaré identities are stated for a real weight, because their consumers are real short
sums.  The Matomäki–Radziwiłł argument applies them to a *Dirichlet polynomial*, whose weight
`a(n)·n^{2πiw}` is complex.  The identity is purely combinatorial — it only redistributes each term
over its designated prime factors with total weight one — so it carries over verbatim:

```text
∑_{n ∈ S} g(n)  =  ∑_{p ∈ P} ∑_{n ∈ S, p ∣ n} g(n)/ω_P(n)  +  ∑_{n ∈ S, ω_P(n) = 0} g(n) ,
```

and, reindexed by the cofactor,

```text
∑_{n ∈ S} g(n)  =  ∑_{p ∈ P} ∑_{m} g(p·m)/ω_P(p·m)  +  (rough part) .
```

Applied to `logPoly` this is the bilinear decomposition of the Dirichlet polynomial that the mean
value theorem and the large-values estimates act on: the designated prime carries the factor
`a(p)·p^{2πiw}` and the cofactor carries the rest.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **Weighted factorization, complex weight.** -/
theorem sum_eq_sum_ramare_complex (P S : Finset ℕ) (g : ℕ → ℂ)
    (hS : ∀ n ∈ S, (primeFactorsIn P n).Nonempty) :
    ∑ n ∈ S, g n
      = ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, g n / ((primeFactorsIn P n).card : ℂ) := by
  classical
  have hswap : ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, g n / ((primeFactorsIn P n).card : ℂ)
      = ∑ p ∈ P, ∑ n ∈ S, (if p ∣ n then g n / ((primeFactorsIn P n).card : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_filter]
  rw [hswap, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hne : (primeFactorsIn P n).Nonempty := hS n hn
  have hcard : 0 < (primeFactorsIn P n).card := Finset.card_pos.2 hne
  have hcard0 : (primeFactorsIn P n).card ≠ 0 := by omega
  have hcardC : ((primeFactorsIn P n).card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hcard0
  rw [← Finset.sum_filter]
  have hfilter : {p ∈ P | p ∣ n} = primeFactorsIn P n := rfl
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Reindexing a sum over multiples of `p` by the cofactor, complex weight. -/
theorem sum_div_image_complex (p : ℕ) (T : Finset ℕ) (hT : ∀ n ∈ T, p ∣ n) (g : ℕ → ℂ) :
    ∑ m ∈ T.image (fun n => n / p), g (p * m) = ∑ n ∈ T, g n := by
  classical
  have hinj : ∀ x ∈ T, ∀ y ∈ T, x / p = y / p → x = y := by
    intro x hx y hy hxy
    have h1 : p * (x / p) = x := Nat.mul_div_cancel' (hT x hx)
    have h2 : p * (y / p) = y := Nat.mul_div_cancel' (hT y hy)
    rw [← h1, ← h2, hxy]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Nat.mul_div_cancel' (hT n hn)]

/-- **Bilinear form, complex weight.** -/
theorem sum_eq_sum_ramare_bilinear_complex (P S : Finset ℕ) (g : ℕ → ℂ)
    (hS : ∀ n ∈ S, (primeFactorsIn P n).Nonempty) :
    ∑ n ∈ S, g n
      = ∑ p ∈ P, ∑ m ∈ ({n ∈ S | p ∣ n}).image (fun n => n / p),
          g (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) := by
  classical
  rw [sum_eq_sum_ramare_complex P S g hS]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine (sum_div_image_complex p _ ?_ _).symm
  intro n hn
  exact (Finset.mem_filter.1 hn).2

/-- **Complete Ramaré decomposition, complex weight.** -/
theorem sum_eq_ramare_add_rough_complex (P S : Finset ℕ) (g : ℕ → ℂ) :
    ∑ n ∈ S, g n
      = (∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, g n / ((primeFactorsIn P n).card : ℂ))
        + ∑ n ∈ {n ∈ S | primeFactorsIn P n = ∅}, g n := by
  classical
  set S' : Finset ℕ := {n ∈ S | (primeFactorsIn P n).Nonempty} with hS'
  have hsplit : ∑ n ∈ S, g n
      = ∑ n ∈ S', g n + ∑ n ∈ {n ∈ S | ¬ (primeFactorsIn P n).Nonempty}, g n := by
    rw [hS']
    exact (Finset.sum_filter_add_sum_filter_not S (fun n => (primeFactorsIn P n).Nonempty) g).symm
  have hrough : {n ∈ S | ¬ (primeFactorsIn P n).Nonempty}
      = {n ∈ S | primeFactorsIn P n = ∅} := by
    refine Finset.filter_congr fun n _ => ?_
    rw [Finset.not_nonempty_iff_eq_empty]
  have hmain : ∑ n ∈ S', g n
      = ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, g n / ((primeFactorsIn P n).card : ℂ) := by
    have hne : ∀ n ∈ S', (primeFactorsIn P n).Nonempty := fun n hn => (Finset.mem_filter.1 hn).2
    rw [sum_eq_sum_ramare_complex P S' g hne]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hsets : {n ∈ S' | p ∣ n} = {n ∈ S | p ∣ n} := by
      ext n
      simp only [hS', Finset.mem_filter]
      constructor
      · rintro ⟨⟨hn, -⟩, hd⟩
        exact ⟨hn, hd⟩
      · rintro ⟨hn, hd⟩
        exact ⟨⟨hn, ⟨p, mem_primeFactorsIn.2 ⟨hp, hd⟩⟩⟩, hd⟩
    rw [hsets]
  rw [hsplit, hrough, hmain]

/-- **The Dirichlet polynomial, Ramaré-decomposed.** -/
theorem logPoly_eq_ramare_add_rough (a : ℕ → ℂ) (P s : Finset ℕ) (w : ℝ) :
    logPoly a s w
      = (∑ p ∈ P, ∑ n ∈ {n ∈ s | p ∣ n},
          (a n * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I))
            / ((primeFactorsIn P n).card : ℂ))
        + ∑ n ∈ {n ∈ s | primeFactorsIn P n = ∅},
            a n * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I) := by
  rw [logPoly]
  exact sum_eq_ramare_add_rough_complex P s
    (fun n => a n * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I))

end RHTower.Sieve

end
