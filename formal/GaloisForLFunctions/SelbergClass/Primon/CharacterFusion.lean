import GaloisForLFunctions.SelbergClass.Primon.SpectralCharacterAlgebra

/-!
# Character fusion and exact triple integrals

The character estimates in Zehavi, §4.1, arXiv:2611.18218, suggest retaining
the full tensor decomposition before integrating. For the corpus's actual
semicircle characters, the Clebsch–Gordan sum is multiplicity-free. The
three-character integral is therefore exactly zero or one, with an explicit
finite admissibility condition.
-/

namespace GaloisForLFunctions.SelbergClass.Primon

open MeasureTheory

/-- The addition identity behind the rank-one tensor product rule. -/
theorem spectralCharacter_addition (m n : ℕ) (x : ℝ) :
    spectralCharacter (m + 1) x * spectralCharacter (n + 1) x -
      spectralCharacter m x * spectralCharacter n x = spectralCharacter (m + n + 2) x := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.zero_add, Nat.add_zero, spectralCharacter_zero, spectralCharacter_one, mul_one]
    rw [spectralCharacter_add_two]
    ring
  | one =>
    have h₀ := spectralCharacter_add_two m x
    have h₁ := spectralCharacter_add_two (m + 1) x
    rw [spectralCharacter_add_two 0 x]
    simp only [Nat.zero_add, spectralCharacter_zero, spectralCharacter_one]
    linear_combination -x * h₀ - h₁
  | more n hn hn1 =>
    have h₀ := spectralCharacter_add_two n x
    have h₁ := spectralCharacter_add_two (n + 1) x
    have ht := spectralCharacter_add_two (m + n + 2) x
    have hidx : m + (n + 2) + 2 = (m + n + 2) + 2 := by omega
    rw [hidx]
    linear_combination x * hn1 - hn +
      spectralCharacter (m + 1) x * h₁ - spectralCharacter m x * h₀ - ht

/-- Tensoring highest weights `m` and `m+n` produces every other weight from `n` to `2m+n`. -/
theorem spectralCharacter_fusion_shifted (m n : ℕ) (x : ℝ) :
    spectralCharacter m x * spectralCharacter (m + n) x =
      ∑ i ∈ Finset.range (m + 1), spectralCharacter (n + 2 * i) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h := spectralCharacter_addition m (m + n) x
    have hi₁ : m + 1 + n = m + n + 1 := by omega
    have hi₂ : m + (m + n) + 2 = n + 2 * (m + 1) := by omega
    rw [hi₁, hi₂] at h ⊢
    linarith only [h]

/-- The unconditional symmetric Clebsch–Gordan formula. -/
theorem spectralCharacter_fusion (m n : ℕ) (x : ℝ) :
    spectralCharacter m x * spectralCharacter n x =
      ∑ i ∈ Finset.range (min m n + 1),
        spectralCharacter (max m n - min m n + 2 * i) x := by
  rcases le_total m n with h | h
  · rw [min_eq_left h, max_eq_right h]
    convert spectralCharacter_fusion_shifted m (n - m) x using 1
    rw [Nat.add_sub_of_le h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]
    convert spectralCharacter_fusion_shifted n (m - n) x using 1
    rw [Nat.add_sub_of_le h]

/-- The admissible third characters occur once each; all other triple integrals vanish. -/
theorem integral_spectralCharacter_triple (m n k : ℕ) :
    (∫ x, spectralCharacter m x * spectralCharacter n x * spectralCharacter k x
      ∂(semicircleSpectralLaw : Measure ℝ)) =
      if ∃ i < min m n + 1, max m n - min m n + 2 * i = k then 1 else 0 := by
  simp_rw [spectralCharacter_fusion, Finset.sum_mul]
  rw [integral_finset_sum]
  · simp_rw [integral_spectralCharacter_mul]
    split_ifs with h
    · obtain ⟨i, hi, hik⟩ := h
      rw [Finset.sum_eq_single i]
      · simp [hik]
      · intro j _ hji
        have hne : max m n - min m n + 2 * j ≠ k := by omega
        exact if_neg hne
      · exact fun hnot => (hnot (Finset.mem_range.mpr hi)).elim
    · apply Finset.sum_eq_zero
      intro i hi
      exact if_neg (fun he => h ⟨i, Finset.mem_range.mp hi, he⟩)
  · intro i _
    exact integrable_semicircleSpectralLaw_continuous
      (spectralCharacter (max m n - min m n + 2 * i) * spectralCharacter k)

/-- A self-tensor character has one copy of every even weight up to twice its degree. -/
theorem integral_spectralCharacter_sq_mul (m k : ℕ) :
    (∫ x, spectralCharacter m x ^ 2 * spectralCharacter (2 * k) x
      ∂(semicircleSpectralLaw : Measure ℝ)) = if k ≤ m then 1 else 0 := by
  simp only [pow_two]
  rw [integral_spectralCharacter_triple]
  congr 1
  simp only [min_self, max_self, Nat.sub_self, zero_add]
  constructor
  · rintro ⟨i, hi, he⟩
    omega
  · intro h
    exact ⟨k, by omega, rfl⟩

end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.spectralCharacter_fusion
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_spectralCharacter_triple
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_spectralCharacter_sq_mul
