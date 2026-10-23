import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ResonatorKroneckerLaw
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# The Cartesian law of the Hecke incidence: the prime part of the surface is a product of towers

Index a positive integer by its exponent vector `n ↦ (v_p(n))_p`. The prime intersection of two
Hecke cycles `Γ_a, Γ_b` is nonzero only when the exponent vectors differ in exactly **one**
coordinate `p`, and then it is the tower weight of the difference
(`heckeIncidence_eq_towerWeight`, `heckeIncidence_eq_zero`):

    Γ_a · Γ_b |_primes = τ_p(|v_p(a) − v_p(b)|)  if v_r(a) = v_r(b) for all r ≠ p,   0 otherwise.

So the incidence graph of the prime part is the **Cartesian product over all primes of the
weighted path graphs** `(ℕ, τ_p(|i − j|))` — the Euler product, read on the scaling surface. On a
lattice test supported on the integers built from a finite set of primes, the prime
self-intersection is the Cartesian (Kronecker) sum of one tower form per prime; the resonator law
`heckeForm_box_eq` is the case of two primes. All coupling between different primes is
archimedean or polar: the Kronecker rank of a test enters the surface only through the collar.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

theorem heckeIncidence_comm (a b : ℕ) : heckeIncidence a b = heckeIncidence b a := by
  rw [heckeIncidence, heckeIncidence, add_comm]

/-- If the exponent vectors of `a ≤ b` agree off `p` and `v_p(a) ≤ v_p(b)`, then
`b = a · p^{v_p(b) − v_p(a)}`. -/
theorem eq_mul_pow_of_factorization {a b p : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hp : p.Prime)
    (h : ∀ r, r ≠ p → a.factorization r = b.factorization r)
    (hle : a.factorization p ≤ b.factorization p) :
    b = a * p ^ (b.factorization p - a.factorization p) := by
  apply Nat.eq_of_factorization_eq hb (mul_ne_zero ha (pow_ne_zero _ hp.ne_zero))
  intro r
  rw [Nat.factorization_mul ha (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_apply]
  by_cases hr : p = r
  · subst hr; simp only [if_true]; omega
  · rw [if_neg hr, add_zero, h r (Ne.symm hr)]

/-- **One differing coordinate**: the prime intersection is the tower weight of the difference. -/
theorem heckeIncidence_eq_towerWeight {a b p : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hp : p.Prime)
    (h : ∀ r, r ≠ p → a.factorization r = b.factorization r) :
    heckeIncidence a b = towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) := by
  -- reduce to `v_p(a) ≤ v_p(b)`
  wlog hle : a.factorization p ≤ b.factorization p generalizing a b
  · rw [heckeIncidence_comm, Nat.dist_comm]
    exact this hb ha (fun r hr => (h r hr).symm) (by omega)
  set k := b.factorization p - a.factorization p
  have hb' : b = a * p ^ k := eq_mul_pow_of_factorization ha hb hp h hle
  have hdist : Nat.dist (a.factorization p) (b.factorization p) = k := Nat.dist_eq_sub_of_le hle
  rw [hdist]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- equal exponent vectors: `a = b`, both atoms vanish
    rw [hk, pow_zero, mul_one] at hb'
    subst hb'
    rw [hk, towerWeight_zero, heckeIncidence, ratioIncidence, if_pos (dvd_refl _), Nat.div_self
      (Nat.pos_of_ne_zero ha)]
    simp [primeAtom]
  · have hdvd : a ∣ b := ⟨_, hb'⟩
    have hndvd : ¬ b ∣ a := by
      intro hba
      have := (Nat.factorization_le_iff_dvd hb ha).mpr hba p
      omega
    have hdiv : b / a = p ^ k := by
      rw [hb', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha)]
    rw [heckeIncidence, ratioIncidence, ratioIncidence, if_pos hdvd, if_neg hndvd, add_zero, hdiv,
      towerWeight]

/-- **Two or more differing coordinates**: no prime intersection. -/
theorem heckeIncidence_eq_zero {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p, p.Prime → ∃ r, r ≠ p ∧ a.factorization r ≠ b.factorization r) :
    heckeIncidence a b = 0 := by
  -- a ratio atom is nonzero only on a prime-power quotient, which differs in one coordinate
  have key : ∀ {x y : ℕ}, x ≠ 0 → y ≠ 0 →
      (∀ p, p.Prime → ∃ r, r ≠ p ∧ x.factorization r ≠ y.factorization r) → ratioIncidence x y = 0 := by
    intro x y hx hy hxy
    unfold ratioIncidence
    split_ifs with hd
    · rw [primeAtom]
      split_ifs with h2
      · have hΛ : ArithmeticFunction.vonMangoldt (y / x) = 0 := by
          rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
          intro hpp
          obtain ⟨p, k, hk, hfac⟩ := isPrimePow_iff_factorization_eq_single.mp hpp
          have hp : p.Prime := by
            have hmem : p ∈ (y / x).factorization.support := by
              rw [hfac, Finsupp.support_single_ne_zero _ hk.ne']; exact Finset.mem_singleton_self p
            exact Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ hmem)
          obtain ⟨r, hrp, hr⟩ := hxy p hp
          apply hr
          have hq := congrArg (fun f => f r) (Nat.factorization_div hd)
          simp only [hfac, Finsupp.single_apply, if_neg (Ne.symm hrp), Finsupp.tsub_apply] at hq
          have hle := (Nat.factorization_le_iff_dvd hx hy).mpr hd r
          omega
        simp [hΛ]
      · rfl
    · rfl
  rw [heckeIncidence, key ha hb h, key hb ha (fun p hp => by
    obtain ⟨r, hr, hne⟩ := h p hp; exact ⟨r, hr, Ne.symm hne⟩), add_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
