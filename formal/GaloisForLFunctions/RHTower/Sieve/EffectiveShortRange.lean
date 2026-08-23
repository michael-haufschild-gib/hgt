import GaloisForLFunctions.RHTower.Sieve.OffDiagonalCorrelationBounds

/-!
# The effective range of the short variable on a dyadic block

On a dyadic block `[P, Q)` of the long variable only the short values whose fibre meets the block
contribute: for every other `m` the masked summand vanishes identically.  The effective range is
therefore `[(A−1)/(Q−1), (B−1)/P]` up to endpoints, of length comparable to `M/P`, which is what
makes the diagonal of the type-II energy proportional to the block length.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- The correlation vanishes when the short value is too large. -/
theorem masked_correlation_eq_zero_of_large {A B P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (T r : ℝ) {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (hbig : (B - 1) / m₁ + 1 ≤ P) :
    (∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)) = 0 := by
  rw [sum_masked_correlation_eq hA hB hP T r hm₁ hm₂,
    Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-- The correlation vanishes when the short value is too small. -/
theorem masked_correlation_eq_zero_of_small {A B P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (T r : ℝ) {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (hsmall : Q ≤ (A - 1) / m₁ + 1) :
    (∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)) = 0 := by
  rw [sum_masked_correlation_eq hA hB hP T r hm₁ hm₂]
  rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-- The masked correlation is conjugate-symmetric in the pair. -/
theorem sum_masked_correlation_conj (T r : ℝ) (A B P Q m₁ m₂ : ℕ) :
    (∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂))
      = (starRingEnd ℂ) (∑ d ∈ Finset.Ico P Q,
          maskedNdExp T r A B d m₂ * (starRingEnd ℂ) (maskedNdExp T r A B d m₁)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

/-- **The effective range of the short variable.** -/
theorem effective_short_range {A B P Q m : ℕ} (hm : 1 ≤ m) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (h1 : ¬ ((B - 1) / m + 1 ≤ P)) (h2 : ¬ (Q ≤ (A - 1) / m + 1)) :
    m ∈ Finset.Ico ((A - 1) / (Q - 1) + 1) ((B - 1) / P + 1) := by
  rw [Finset.mem_Ico]
  constructor
  · have hlt : (A - 1) / m < Q - 1 := by omega
    have hnot : ¬ ((Q - 1) * m ≤ A - 1) := by
      intro hcon
      have := (Nat.le_div_iff_mul_le (by omega : 0 < m)).2 hcon
      omega
    have hlt2 : A - 1 < (Q - 1) * m := by omega
    have := (Nat.div_lt_iff_lt_mul (by omega : 0 < Q - 1)).2 (by
      rw [Nat.mul_comm] at hlt2
      exact hlt2)
    omega
  · have hle : P ≤ (B - 1) / m := by omega
    have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < m)).1 hle
    have hcomm : m * P ≤ B - 1 := by
      rw [Nat.mul_comm]
      exact hmul
    have := (Nat.le_div_iff_mul_le (by omega : 0 < P)).2 hcomm
    omega

end

end RHTower.Sieve
