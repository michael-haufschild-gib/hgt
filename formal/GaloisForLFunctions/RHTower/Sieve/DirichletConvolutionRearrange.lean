import GaloisForLFunctions.RHTower.Sieve.DivisorSquareMoment

/-!
# Summing a Dirichlet convolution against a weight over a finite range

Every piece of Vaughan's identity is a Dirichlet convolution summed against `e(F(n))` over a block.
Rearranging it into a double sum over the two factors — with the block constraint kept as a
filter on the product — is the step that turns Vaughan's identity into type-I and type-II forms.
-/

namespace RHTower.Sieve

open Finset

/-- **The convolution rearrangement.**  Summing `f ∗ g` against a weight over a block is summing
the product over the pairs whose product lies in the block. -/
theorem sum_conv_mul_eq {I : Finset ℕ} {L : ℕ} (hI : ∀ n ∈ I, 1 ≤ n ∧ n ≤ L)
    (f g w : ℕ → ℂ) :
    (∑ n ∈ I, (∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2) * w n)
      = ∑ p ∈ (Finset.Icc 1 L ×ˢ Finset.Icc 1 L).filter (fun p => p.1 * p.2 ∈ I),
          f p.1 * g p.2 * w (p.1 * p.2) := by
  classical
  have hstep : (∑ n ∈ I, (∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2) * w n)
      = ∑ n ∈ I, ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2 * w n :=
    Finset.sum_congr rfl fun n _ => Finset.sum_mul _ _ _
  rw [hstep, Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => x.2) (fun p => ⟨p.1 * p.2, p⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d, k⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨hnI, hprod, hn0⟩ := hx
    obtain ⟨hn1, hnL⟩ := hI n hnI
    have hd1 : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · simp at hprod; omega
      · exact h
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hprod; omega
      · exact h
    have hdL : d ≤ L := by
      have : d ≤ n := by
        calc d = d * 1 := by ring
          _ ≤ d * k := Nat.mul_le_mul_left d hk1
          _ = n := hprod
      omega
    have hkL : k ≤ L := by
      have : k ≤ n := by
        calc k = 1 * k := by ring
          _ ≤ d * k := Nat.mul_le_mul_right k hd1
          _ = n := hprod
      omega
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hd1, hdL⟩, ⟨hk1, hkL⟩⟩, by rw [hprod]; exact hnI⟩
  · rintro ⟨d, k⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hd1, hdL⟩, hk1, hkL⟩, hmem⟩ := hp
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal]
    exact ⟨hmem, trivial, Nat.mul_ne_zero (by omega) (by omega)⟩
  · rintro ⟨n, d, k⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨-, hprod, -⟩ := hx
    simp [hprod]
  · rintro ⟨d, k⟩ _
    rfl
  · rintro ⟨n, d, k⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨-, hprod, -⟩ := hx
    simp [hprod]

end RHTower.Sieve
