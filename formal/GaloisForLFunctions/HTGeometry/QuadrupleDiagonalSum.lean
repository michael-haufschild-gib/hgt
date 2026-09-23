import Mathlib

/-!
# A four-fold sum supported on two diagonals

If the constraint `p·r = q·t` cuts out exactly the two diagonals `(p = q, r = t)` and
`(p = t, r = q)` — as it does when the indices are prime — then the four-fold sum

```text
∑_{p,q,r,t ∈ s}  [p r = q t] · a_p a_q a_r a_t
```

collapses to `2 A² − ∑ a_p⁴` with `A = ∑ a_p²`: each diagonal contributes `A²`, and their overlap,
the full diagonal `p = q = r = t`, is counted twice and must be removed once.

This is the combinatorial heart of the fourth-moment identity for a random series with independent
unimodular coefficients.  It is stated over an arbitrary commutative ring and with the diagonal
description as a hypothesis, so that the arithmetic input — unique factorisation of a product of two
primes — stays separated from the summation.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R]

/-- The pointwise decomposition of the constrained summand into the two diagonals minus their
overlap. -/
theorem diagonal_summand_eq {s : Finset ℕ} (a : ℕ → R) {p q r t : ℕ}
    (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s) (ht : t ∈ s)
    (hsplit : ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, ∀ t ∈ s,
      p * r = q * t ↔ ((p = q ∧ r = t) ∨ (p = t ∧ r = q))) :
    (if p * r = q * t then a p * a q * a r * a t else 0)
      = (if p = q then a p * a q else 0) * (if r = t then a r * a t else 0)
        + (if p = t then a p * a t else 0) * (if q = r then a q * a r else 0)
        - (if p = q ∧ q = r ∧ r = t then a p ^ (4 : ℕ) else 0) := by
  have hiff := hsplit p hp q hq r hr t ht
  simp only [hiff]
  by_cases h1 : p = q <;> by_cases h2 : r = t <;> by_cases h3 : p = t <;>
    by_cases h4 : q = r <;> subst_vars <;> simp_all <;>
    try (intro hcon; subst hcon; simp_all)
  all_goals ring

/-- The one-dimensional diagonal sum. -/
theorem sum_ite_eq_sq (s : Finset ℕ) (a : ℕ → R) {p : ℕ} (hp : p ∈ s) :
    (∑ q ∈ s, if p = q then a p * a q else 0) = a p ^ (2 : ℕ) := by
  classical
  rw [Finset.sum_ite_eq s p fun q => a p * a q, if_pos hp]
  ring

/-- The reversed one-dimensional diagonal sum. -/
theorem sum_ite_eq_sq' (s : Finset ℕ) (a : ℕ → R) {p : ℕ} (hp : p ∈ s) :
    (∑ t ∈ s, if p = t then a p * a t else 0) = a p ^ (2 : ℕ) :=
  sum_ite_eq_sq s a hp

/-- **The four-fold sum on two diagonals.** -/
theorem quadruple_diagonal_sum (s : Finset ℕ) (a : ℕ → R)
    (hsplit : ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, ∀ t ∈ s,
      p * r = q * t ↔ ((p = q ∧ r = t) ∨ (p = t ∧ r = q))) :
    (∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
        (if p * r = q * t then a p * a q * a r * a t else 0))
      = 2 * (∑ p ∈ s, a p ^ (2 : ℕ)) ^ (2 : ℕ) - ∑ p ∈ s, a p ^ (4 : ℕ) := by
  classical
  set A : R := ∑ p ∈ s, a p ^ (2 : ℕ) with hAdef
  -- collapse the innermost sum
  have hinner : ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s,
      (∑ t ∈ s, (if p * r = q * t then a p * a q * a r * a t else 0))
        = (if p = q then a p * a q else 0) * a r ^ (2 : ℕ)
          + a p ^ (2 : ℕ) * (if q = r then a q * a r else 0)
          - (if p = q ∧ q = r then a p ^ (4 : ℕ) else 0) := by
    intro p hp q hq r hr
    have hcongr : (∑ t ∈ s, (if p * r = q * t then a p * a q * a r * a t else 0))
        = ∑ t ∈ s, ((if p = q then a p * a q else 0) * (if r = t then a r * a t else 0)
            + (if p = t then a p * a t else 0) * (if q = r then a q * a r else 0)
            - (if p = q ∧ q = r ∧ r = t then a p ^ (4 : ℕ) else 0)) :=
      Finset.sum_congr rfl fun t ht => diagonal_summand_eq a hp hq hr ht hsplit
    rw [hcongr, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 1
    · congr 1
      · rw [← Finset.mul_sum, sum_ite_eq_sq s a hr]
      · rw [← Finset.sum_mul, sum_ite_eq_sq' s a hp]
    · have hstep : ∀ t : ℕ, (if p = q ∧ q = r ∧ r = t then a p ^ (4 : ℕ) else 0)
          = (if r = t then (if p = q ∧ q = r then a p ^ (4 : ℕ) else 0) else 0) := by
        intro t
        rcases eq_or_ne r t with rfl | hne
        · rw [if_pos rfl]
          by_cases hc : p = q ∧ q = r
          · rw [if_pos ⟨hc.1, hc.2, rfl⟩, if_pos hc]
          · rw [if_neg (fun hd => hc ⟨hd.1, hd.2.1⟩), if_neg hc]
        · rw [if_neg hne, if_neg (fun hd => hne hd.2.2)]
      simp_rw [hstep]
      rw [Finset.sum_ite_eq s r fun _ => (if p = q ∧ q = r then a p ^ (4 : ℕ) else 0), if_pos hr]
  -- collapse the third sum
  have hthird : ∀ p ∈ s, ∀ q ∈ s,
      (∑ r ∈ s, ∑ t ∈ s, (if p * r = q * t then a p * a q * a r * a t else 0))
        = (if p = q then a p * a q else 0) * A + a p ^ (2 : ℕ) * a q ^ (2 : ℕ)
          - (if p = q then a p ^ (4 : ℕ) else 0) := by
    intro p hp q hq
    have hcongr := Finset.sum_congr rfl fun r hr => hinner p hp q hq r hr
    rw [hcongr, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 1
    · congr 1
      · rw [← Finset.mul_sum, ← hAdef]
      · rw [← Finset.mul_sum, sum_ite_eq_sq s a hq]
    · have hstep : ∀ r : ℕ, (if p = q ∧ q = r then a p ^ (4 : ℕ) else 0)
          = (if q = r then (if p = q then a p ^ (4 : ℕ) else 0) else 0) := by
        intro r
        rcases eq_or_ne q r with rfl | hne
        · rw [if_pos rfl]
          by_cases hc : p = q
          · rw [if_pos ⟨hc, rfl⟩, if_pos hc]
          · rw [if_neg (fun hd => hc hd.1), if_neg hc]
        · rw [if_neg hne, if_neg (fun hd => hne hd.2)]
      simp_rw [hstep]
      rw [Finset.sum_ite_eq s q fun _ => (if p = q then a p ^ (4 : ℕ) else 0), if_pos hq]
  -- collapse the second sum
  have hsecond : ∀ p ∈ s,
      (∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s, (if p * r = q * t then a p * a q * a r * a t else 0))
        = 2 * (a p ^ (2 : ℕ) * A) - a p ^ (4 : ℕ) := by
    intro p hp
    have hcongr := Finset.sum_congr rfl fun q hq => hthird p hp q hq
    rw [hcongr, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h1 : (∑ q ∈ s, (if p = q then a p * a q else 0) * A) = a p ^ (2 : ℕ) * A := by
      rw [← Finset.sum_mul, sum_ite_eq_sq s a hp]
    have h2 : (∑ q ∈ s, a p ^ (2 : ℕ) * a q ^ (2 : ℕ)) = a p ^ (2 : ℕ) * A := by
      rw [← Finset.mul_sum, ← hAdef]
    have h3 : (∑ q ∈ s, (if p = q then a p ^ (4 : ℕ) else 0)) = a p ^ (4 : ℕ) := by
      rw [Finset.sum_ite_eq s p fun _ => a p ^ (4 : ℕ), if_pos hp]
    rw [h1, h2, h3]
    ring
  have hfinal := Finset.sum_congr rfl fun p hp => hsecond p hp
  rw [hfinal, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← hAdef]
  ring

end GaloisForLFunctions.HTGeometry

end
