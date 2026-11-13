import GaloisForLFunctions.goldbach.OddCharacterProjection
import GaloisForLFunctions.goldbach.ProductResidueProfile

/-!
# Character moments of the multiplication profile

The complete multiplication profile and its balanced-block realization are
even under residue negation. Their odd-character moments vanish. More
precisely, their full multiplicative-character transforms are supported at
the principal character, although their additive Fourier transforms retain
the nonconstant gcd spectrum.
-/

namespace GaloisForLFunctions.Goldbach

open Finset
open scoped Classical

noncomputable section

/-- Negating one multiplicand gives an exact symmetry of the product distribution. -/
theorem productResidueCount_neg (q : ℕ+) (r : ZMod (q : ℕ)) :
    productResidueCount q (-r) = productResidueCount q r := by
  unfold productResidueCount
  apply Fintype.sum_equiv (Equiv.neg _) _ _
  intro a
  apply sum_congr rfl
  intro b _
  simp only [Equiv.neg_apply, neg_mul, neg_eq_iff_eq_neg]

/-- Complete balanced blocks preserve the same negation symmetry. -/
theorem balancedProductResidueCount_neg (q : ℕ+) (k : ℕ) (r : ZMod (q : ℕ)) :
    balancedProductResidueCount q k (-r) = balancedProductResidueCount q k r := by
  rw [balancedProductResidueCount_eq, balancedProductResidueCount_eq, productResidueCount_neg]

/-- Multiplicative characters see only the principal mode of the complete product profile. -/
theorem productResidueCount_character (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ)) :
    (∑ r : ZMod (q : ℕ), (productResidueCount q r : ℂ) * χ r) =
      if χ = 1 then ((q : ℕ).totient : ℂ) ^ 2 else 0 := by
  rw [productResidueCount_pairing]
  simp_rw [map_mul]
  rw [← sum_mul_sum]
  by_cases h : χ = 1
  · subst χ
    rw [if_pos rfl, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, pow_two]
  · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one h, zero_mul]

/-- The balanced interval realization has exactly the same single multiplicative mode. -/
theorem balancedProductResidueCount_character (q : ℕ+) (k : ℕ)
    (χ : DirichletCharacter ℂ (q : ℕ)) :
    (∑ r : ZMod (q : ℕ), (balancedProductResidueCount q k r : ℂ) * χ r) =
      (k : ℂ) ^ 2 * (if χ = 1 then ((q : ℕ).totient : ℂ) ^ 2 else 0) := by
  simp only [balancedProductResidueCount_eq, Nat.cast_mul, Nat.cast_pow, mul_assoc]
  rw [← mul_sum, productResidueCount_character]

/-- The odd-character projection annihilates the real complete-product profile exactly. -/
theorem productResidueCount_odd_character_moment (N : ℕ) :
    (∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
      ‖unitCharacterSum N
        (fun u => (productResidueCount ⟨N + 1, Nat.succ_pos N⟩ u : ℂ)) χ‖ ^ 2) = 0 := by
  have h := four_mul_odd_moment_eq_reflection_defect N
    (fun u => (productResidueCount ⟨N + 1, Nat.succ_pos N⟩ u : ℝ))
  simp only [Units.val_neg, productResidueCount_neg, sub_self, zero_pow two_ne_zero,
    sum_const_zero, mul_zero, Nat.cast_ofNat] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- The same annihilation holds for every complete balanced product block. -/
theorem balancedProductResidueCount_odd_character_moment (N k : ℕ) :
    (∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
      ‖unitCharacterSum N
        (fun u => (balancedProductResidueCount ⟨N + 1, Nat.succ_pos N⟩ k u : ℂ)) χ‖ ^ 2) = 0 := by
  have h := four_mul_odd_moment_eq_reflection_defect N
    (fun u => (balancedProductResidueCount ⟨N + 1, Nat.succ_pos N⟩ k u : ℝ))
  simp only [Units.val_neg, balancedProductResidueCount_neg, sub_self, zero_pow two_ne_zero,
    sum_const_zero, mul_zero, Nat.cast_ofNat] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

end

end GaloisForLFunctions.Goldbach
