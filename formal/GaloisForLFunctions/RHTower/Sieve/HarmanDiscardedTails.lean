import GaloisForLFunctions.RHTower.Sieve.HarmanMinorant

/-!
# The two discarded Harman tails

Harman's minorant `rhoMinus z Q D E` is the sifting function `ρ(·, Q)` minus two nonnegative tails:
the second Buchstab sum over the inadmissible pairs (`q₁ ≥ D` or `q₁ q₂⁴ ≥ E`) at level `q₂`, and
the fourth Buchstab sum at level `q₄` below the admissible triples.  This is an exact identity.
-/

namespace RHTower.Sieve

open Finset

/-- The second Buchstab sum over the inadmissible pairs. -/
def harmanDiscardPairSum (z Q D E n : ℕ) : ℕ :=
  ∑ q₁ ∈ primeWindow n z Q, ∑ q₂ ∈ (primeWindow (n / q₁) z q₁).filter
    (fun q₂ => ¬ (q₁ < D ∧ q₁ * q₂ ^ (4 : ℕ) < E)), rho (n / q₁ / q₂) q₂

/-- The fourth Buchstab sum below the admissible triples. -/
def harmanDiscardQuadrupleSum (z D E n : ℕ) : ℕ :=
  ∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ harmanPairs z E n q₁,
    ∑ q₃ ∈ primeWindow (n / q₁ / q₂) z q₂,
      ∑ q₄ ∈ primeWindow (n / q₁ / q₂ / q₃) z q₃, rho (n / q₁ / q₂ / q₃ / q₄) q₄

theorem primeWindow_filter_lt {n z D Q : ℕ} (hDQ : D ≤ Q) :
    (primeWindow n z Q).filter (· < D) = primeWindow n z D := by
  ext q
  simp only [primeWindow, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, by omega⟩, h3⟩, h2⟩

theorem harmanR2adm_eq_filter {z Q D E n : ℕ} (hDQ : D ≤ Q) :
    harmanR2adm z D E n = ∑ q₁ ∈ primeWindow n z Q, ∑ q₂ ∈ (primeWindow (n / q₁) z q₁).filter
      (fun q₂ => q₁ < D ∧ q₁ * q₂ ^ (4 : ℕ) < E), rho (n / q₁ / q₂) q₂ := by
  unfold harmanR2adm
  rw [← primeWindow_filter_lt (n := n) (z := z) hDQ, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q₁ _ => ?_)
  by_cases hD : q₁ < D
  · rw [if_pos hD]
    unfold harmanPairs
    exact Finset.sum_congr (Finset.filter_congr (fun q₂ _ => by simp [hD])) (fun _ _ => rfl)
  · rw [if_neg hD, eq_comm]
    refine Finset.sum_eq_zero (fun q₂ hq₂ => ?_)
    exact absurd (Finset.mem_filter.1 hq₂).2.1 hD

theorem harmanR2_eq_adm_add_discard {z Q D E n : ℕ} (hDQ : D ≤ Q) :
    harmanR2 z Q n = harmanR2adm z D E n + harmanDiscardPairSum z Q D E n := by
  rw [harmanR2adm_eq_filter hDQ]
  unfold harmanR2 harmanDiscardPairSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun q₁ _ => ?_)
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem harmanS3_eq_R3_add_discard {z D E n : ℕ} (hn : 0 < n) :
    harmanS3 z D E n = harmanR3 z D E n + harmanDiscardQuadrupleSum z D E n := by
  unfold harmanS3 harmanR3 harmanDiscardQuadrupleSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun q₁ hq₁ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun q₂ hq₂ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun q₃ hq₃ => ?_)
  have hq₂' : q₂ ∈ primeWindow (n / q₁) z q₁ := Finset.mem_of_mem_filter _ hq₂
  have h1 : 0 < n / q₁ := div_pos_of_mem_primeWindow hn hq₁
  have h2 : 0 < n / q₁ / q₂ := div_pos_of_mem_primeWindow h1 hq₂'
  have h3 : 0 < n / q₁ / q₂ / q₃ := div_pos_of_mem_primeWindow h2 hq₃
  exact (buchstab_window h3 (mem_primeWindow.1 hq₃).1.1).symm

/-- **Harman's identity.**  `ρ(n, Q) = ρ⁻(n) + D₂(n) + D₄(n)`. -/
theorem rho_eq_rhoMinus_add_discards {z Q D E n : ℕ} (hn : 0 < n) (hzQ : z ≤ Q) (hDQ : D ≤ Q) :
    (rho n Q : ℤ) = rhoMinus z Q D E n + harmanDiscardPairSum z Q D E n
      + harmanDiscardQuadrupleSum z D E n := by
  have h1 : (rho n Q : ℤ) + (harmanR1 z Q n : ℤ) = (rho n z : ℤ) := by
    exact_mod_cast harman_step_one hn hzQ
  have h2 : (harmanS1 z Q n : ℤ) = (harmanR1 z Q n : ℤ) + (harmanR2 z Q n : ℤ) := by
    exact_mod_cast harman_step_two (z := z) (Q := Q) hn
  have h3 : (harmanS2 z D E n : ℤ) = (harmanR2adm z D E n : ℤ) + (harmanR3 z D E n : ℤ) := by
    exact_mod_cast harman_step_three (z := z) (D := D) (E := E) hn
  have h4 : (harmanR2 z Q n : ℤ) = (harmanR2adm z D E n : ℤ) + (harmanDiscardPairSum z Q D E n : ℤ) := by
    exact_mod_cast harmanR2_eq_adm_add_discard (E := E) hDQ
  have h5 : (harmanS3 z D E n : ℤ) = (harmanR3 z D E n : ℤ) + (harmanDiscardQuadrupleSum z D E n : ℤ) := by
    exact_mod_cast harmanS3_eq_R3_add_discard hn
  rw [rhoMinus]
  linarith

/-- On `[Q, Q²)` the minorant is the prime indicator minus the two discarded tails. -/
theorem rhoMinus_eq_prime_sub_discards {z Q D E n : ℕ} (hn : 0 < n) (hQ : 2 ≤ Q) (hzQ : z ≤ Q)
    (hDQ : D ≤ Q) (hQn : Q ≤ n) (hnQ : n < Q * Q) :
    rhoMinus z Q D E n = (if n.Prime then 1 else 0 : ℤ) - harmanDiscardPairSum z Q D E n
      - harmanDiscardQuadrupleSum z D E n := by
  have h := rho_eq_rhoMinus_add_discards (E := E) hn hzQ hDQ
  rw [rho_eq_prime_indicator hQ hQn hnQ] at h
  by_cases hp : n.Prime <;> simp only [hp, if_true, if_false] at h ⊢ <;> push_cast at h <;> linarith

end RHTower.Sieve
