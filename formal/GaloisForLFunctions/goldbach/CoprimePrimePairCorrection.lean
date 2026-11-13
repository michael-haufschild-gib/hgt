import GaloisForLFunctions.goldbach.RiemannHypothesisBridge

/-!
# The exact coprimality correction for prime pairs

Among two primes, failure of coprimality with their sum is exactly equality
of the primes. Consequently the reduced-residue prime-pair weight differs
from the full Goldbach weight only by its possible central diagonal.
This is the finite correction underlying Li--Liu, Proposition B.1.
-/

namespace GaloisForLFunctions.Goldbach

open Finset

noncomputable section

/-- Prime-pair weight retained by characters modulo the target. -/
def coprimePrimePairWeight (N : ℕ) : ℝ :=
  ∑ p ∈ antidiagonal N,
    if p.1.Coprime N then primeLogWeight p.1 * primeLogWeight p.2 else 0

/-- Coprimality removes precisely the diagonal from a pair of prime weights. -/
theorem primeLogWeight_mul_coprime_decomposition (p q : ℕ) :
    primeLogWeight p * primeLogWeight q =
      (if p.Coprime (p + q) then primeLogWeight p * primeLogWeight q else 0) +
        if p = q then primeLogWeight p ^ 2 else 0 := by
  by_cases hp : p.Prime
  · by_cases hq : q.Prime
    · have hc : p.Coprime (p + q) ↔ p ≠ q := by
        rw [Nat.coprime_self_add_right, hp.coprime_iff_not_dvd,
          hq.dvd_iff_eq hp.ne_one]
        exact ne_comm
      by_cases he : p = q
      · subst q
        simp only [hc, ne_eq, not_true_eq_false, if_false, if_true, zero_add, pow_two]
      · simp only [hc, he, ne_eq, not_false_eq_true, if_true, if_false, add_zero]
    · have he : p ≠ q := fun h => hq (h ▸ hp)
      simp [primeLogWeight, hq, he]
  · simp [primeLogWeight, hp]

private theorem diagonal_primePairWeight (N : ℕ) :
    (∑ p ∈ antidiagonal N, if p.1 = p.2 then primeLogWeight p.1 ^ 2 else 0) =
      if N % 2 = 0 then primeLogWeight (N / 2) ^ 2 else 0 := by
  by_cases hN : N % 2 = 0
  · rw [if_pos hN]
    have hm : (N / 2, N / 2) ∈ antidiagonal N := mem_antidiagonal.mpr (by omega)
    rw [sum_eq_single (N / 2, N / 2)]
    · simp only [if_true]
    · intro p hp hne
      have hpN := mem_antidiagonal.mp hp
      have hneq : p.1 ≠ p.2 := by
        intro he
        apply hne
        apply Prod.ext <;> omega
      exact if_neg hneq
    · exact fun h => False.elim (h hm)
  · rw [if_neg hN]
    apply sum_eq_zero
    intro p hp
    have hpN := mem_antidiagonal.mp hp
    exact if_neg (by omega)

/-- The full count is the character-visible count plus one possible central prime pair. -/
theorem primePairWeight_eq_coprime_add_diagonal (N : ℕ) :
    primePairWeight N = coprimePrimePairWeight N +
      if N % 2 = 0 then primeLogWeight (N / 2) ^ 2 else 0 := by
  rw [← diagonal_primePairWeight, coprimePrimePairWeight, ← sum_add_distrib]
  unfold primePairWeight additivePairWeight
  apply sum_congr rfl
  intro p hp
  have hN := mem_antidiagonal.mp hp
  simpa only [hN] using primeLogWeight_mul_coprime_decomposition p.1 p.2

/-- Strict positivity of the reduced count detects distinct primes exactly. -/
theorem coprimePrimePairWeight_pos_iff (N : ℕ) :
    0 < coprimePrimePairWeight N ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = N := by
  have hnn (p : ℕ × ℕ) :
      0 ≤ if p.1.Coprime N then primeLogWeight p.1 * primeLogWeight p.2 else 0 := by
    split_ifs
    · exact mul_nonneg (primeLogWeight_nonneg _) (primeLogWeight_nonneg _)
    · exact le_rfl
  rw [coprimePrimePairWeight, sum_pos_iff_of_nonneg (fun p _ => hnn p)]
  constructor
  · rintro ⟨⟨p,q⟩, hpq, h⟩
    have hs := mem_antidiagonal.mp hpq
    split_ifs at h with hc
    · have hpos := (mul_pos_iff.mp h).resolve_right
        (fun hn => (not_lt_of_ge (primeLogWeight_nonneg p)) hn.1)
      have hp : 0 < primeLogWeight p := hpos.1
      have hq : 0 < primeLogWeight q := hpos.2
      have hprime := (primeLogWeight_pos_iff p).mp hp
      refine ⟨p,q,hprime,(primeLogWeight_pos_iff q).mp hq,?_,hs⟩
      intro he
      rw [← hs, he, Nat.coprime_self_add_right, Nat.coprime_self] at hc
      exact hprime.ne_one (he.trans hc)
    · exact False.elim (lt_irrefl 0 h)
  · rintro ⟨p,q,hp,hq,hne,hs⟩
    refine ⟨(p,q), mem_antidiagonal.mpr hs, ?_⟩
    have hc : p.Coprime N := by
      rw [← hs, Nat.coprime_self_add_right, hp.coprime_iff_not_dvd,
        hq.dvd_iff_eq hp.ne_one]
      exact Ne.symm hne
    rw [if_pos hc]
    exact mul_pos ((primeLogWeight_pos_iff p).mpr hp) ((primeLogWeight_pos_iff q).mpr hq)

end

end GaloisForLFunctions.Goldbach

-- Temporary dependency audit.
#print axioms GaloisForLFunctions.Goldbach.coprimePrimePairWeight
#print axioms GaloisForLFunctions.Goldbach.primeLogWeight_mul_coprime_decomposition
#print axioms GaloisForLFunctions.Goldbach.primePairWeight_eq_coprime_add_diagonal
#print axioms GaloisForLFunctions.Goldbach.coprimePrimePairWeight_pos_iff
