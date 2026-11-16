import GaloisForLFunctions.BiarithmeticGeometry.Affine.CharacterOnsager
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic

/-!
# Four-term character cancellation is pairwise

Four unit complex phases sum to zero exactly when they split into two
opposite pairs. This geometric part of the short-root-sum classification
applies to every finite additive character. In odd cyclic order, no such
four-term cancellation is possible, even with repeated phases.
-/

noncomputable section
open scoped ComplexConjugate
namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem four_unit_phases_pair (a b c d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hs : a + b + c + d = 0) :
    (a + b = 0 ∧ c + d = 0) ∨ (a + c = 0 ∧ b + d = 0) ∨
      (a + d = 0 ∧ b + c = 0) := by
  have ha0 : a ≠ 0 := by intro h; simp only [h, norm_zero] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := by intro h; simp only [h, norm_zero] at hb; exact zero_ne_one hb
  have hc0 : c ≠ 0 := by intro h; simp only [h, norm_zero] at hc; exact zero_ne_one hc
  have hd0 : d ≠ 0 := by intro h; simp only [h, norm_zero] at hd; exact zero_ne_one hd
  have hi := congrArg conj hs
  simp only [map_add, map_zero, ← Complex.inv_eq_conj ha, ← Complex.inv_eq_conj hb,
    ← Complex.inv_eq_conj hc, ← Complex.inv_eq_conj hd] at hi
  field_simp [ha0, hb0, hc0, hd0] at hi
  have hp : (a + b) * (a + c) * (a + d) = 0 := by
    linear_combination a ^ 2 * hs + hi
  rcases mul_eq_zero.mp hp with hp | hp
  · rcases mul_eq_zero.mp hp with hp | hp
    · left
      exact ⟨hp, by linear_combination hs - hp⟩
    · right; left
      exact ⟨hp, by linear_combination hs - hp⟩
  · right; right
    exact ⟨hp, by linear_combination hs - hp⟩

/-- Every four-term cancellation in a finite character splits into opposite pairs. -/
theorem finiteCharacter_four_term_zero_iff {G : Type*} [AddCommGroup G] [Finite G]
    (χ : AddChar G ℂ) (a b c d : G) :
    χ a + χ b + χ c + χ d = 0 ↔
      (χ a + χ b = 0 ∧ χ c + χ d = 0) ∨
      (χ a + χ c = 0 ∧ χ b + χ d = 0) ∨
      (χ a + χ d = 0 ∧ χ b + χ c = 0) := by
  constructor
  · exact four_unit_phases_pair _ _ _ _ (χ.norm_apply a) (χ.norm_apply b)
      (χ.norm_apply c) (χ.norm_apply d)
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linear_combination h₁ + h₂

private theorem odd_cyclic_character_pair_ne_zero (k : ℕ)
    (χ : AddChar (ZMod (2 * k + 1)) ℂ) (a b : ZMod (2 * k + 1)) : χ a + χ b ≠ 0 := by
  have hp (x : ZMod (2 * k + 1)) : χ x ^ (2 * k + 1) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  intro h
  have he : χ a = -χ b := eq_neg_of_add_eq_zero_left h
  have hpow := hp a
  rw [he, pow_add, pow_mul, neg_sq, pow_one, mul_neg] at hpow
  have hbpow := hp b
  rw [pow_add, pow_mul, pow_one] at hbpow
  rw [hbpow] at hpow
  norm_num at hpow

/-- Odd cyclic spectra have no four-term vanishing phase sum, including repeated phases. -/
theorem odd_cyclic_four_term_ne_zero (k : ℕ)
    (χ : AddChar (ZMod (2 * k + 1)) ℂ) (a b c d : ZMod (2 * k + 1)) :
    χ a + χ b + χ c + χ d ≠ 0 := by
  letI : NeZero (2 * k + 1) := ⟨by omega⟩
  intro h
  rcases (finiteCharacter_four_term_zero_iff χ a b c d).mp h with h | h | h
  · exact odd_cyclic_character_pair_ne_zero k χ a b h.1
  · exact odd_cyclic_character_pair_ne_zero k χ a c h.1
  · exact odd_cyclic_character_pair_ne_zero k χ a d h.1


/-- Odd cyclic symmetric translation has no zero mode. Fourier duality turns this
into the impossibility of two opposite odd-order character values. -/
theorem oddCyclic_symmetricTranslation_eq_zero_iff (k : ℕ)
    (f : ZMod (2 * k + 1) → ℂ) :
    symmetricTranslation (1 : ZMod (2 * k + 1)) f = 0 ↔ f = 0 := by
  letI : NeZero (2 * k + 1) := ⟨by omega⟩
  constructor
  · intro h
    apply ZMod.dft.injective
    rw [map_zero]
    have hd := congrArg ZMod.dft h
    rw [finiteCyclic_fourier_translation, map_zero] at hd
    ext x
    have hx := congrFun hd x
    simp only [characterCosineClock_apply, Pi.zero_apply] at hx
    exact (mul_eq_zero.mp hx).resolve_left
      (odd_cyclic_character_pair_ne_zero k ZMod.stdAddChar x (-x))
  · rintro rfl
    exact map_zero _

/-- On odd cyclic inertia spaces, symmetric translation is an automorphism. -/
theorem oddCyclic_symmetricTranslation_bijective (k : ℕ) :
    Function.Bijective (symmetricTranslation (1 : ZMod (2 * k + 1))) := by
  letI : NeZero (2 * k + 1) := ⟨by omega⟩
  have hi : Function.Injective (symmetricTranslation (1 : ZMod (2 * k + 1))) := by
    intro f g h
    apply sub_eq_zero.mp
    apply (oddCyclic_symmetricTranslation_eq_zero_iff k (f - g)).mp
    rw [map_sub, h, sub_self]
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

end GaloisForLFunctions.BiarithmeticGeometry

#print axioms GaloisForLFunctions.BiarithmeticGeometry.finiteCharacter_four_term_zero_iff
#print axioms GaloisForLFunctions.BiarithmeticGeometry.odd_cyclic_four_term_ne_zero

#print axioms GaloisForLFunctions.BiarithmeticGeometry.oddCyclic_symmetricTranslation_bijective
