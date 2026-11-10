import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitExchanges
import Mathlib.RingTheory.Coprime.Basic

/-!
# Shifting digit exponents

A uniform exponent shift preserves the number of digit occurrences and
multiplies their value by a power of p. This factor is coprime to p^s−1,
so divisibility is preserved in both directions. Residue contents and their
inverse coordinates undergo the corresponding cyclic translation.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Raising every digit exponent by the same amount preserves the digit multiplicity bound. -/
def shiftDigit {p : ℕ} (d : ℕ) (x : Digit p) : Digit p := (x.1 + d, x.2)

theorem shiftDigit_injective {p : ℕ} (d : ℕ) : Function.Injective (shiftDigit (p := p) d) := by
  intro x y h
  have hf : x.1 + d = y.1 + d := congrArg (fun t : Digit p => t.1) h
  have hs := congrArg (fun t : Digit p => t.2) h
  exact Prod.ext (Nat.add_right_cancel hf) (by simpa only [shiftDigit] using hs)

def shiftDigits {p : ℕ} (d : ℕ) (S : Finset (Digit p)) : Finset (Digit p) :=
  S.image (shiftDigit d)

theorem card_shiftDigits {p : ℕ} (d : ℕ) (S : Finset (Digit p)) :
    (shiftDigits d S).card = S.card := card_image_of_injective S (shiftDigit_injective d)

theorem digitValue_shiftDigits {p : ℕ} (d : ℕ) (S : Finset (Digit p)) :
    digitValue p (shiftDigits d S) = digitValue p S * (p : ℤ) ^ d := by
  unfold shiftDigits digitValue tokenValue
  rw [sum_image]
  · simp only [shiftDigit, pow_add, sum_mul]
  · exact fun x _ y _ h => shiftDigit_injective d h

/-- The modulus p^s−1 is coprime to every power of p. -/
theorem isCoprime_modulus_pow (p s d : ℕ) (hs : 0 < s) :
    IsCoprime ((p : ℤ) ^ s - 1) ((p : ℤ) ^ d) := by
  apply IsCoprime.pow_right
  refine ⟨-1, (p : ℤ) ^ (s - 1), ?_⟩
  have he : s = (s - 1) + 1 := by omega
  nth_rw 1 [he]
  rw [pow_succ]
  ring

theorem dvd_digitValue_shiftDigits_iff {p s : ℕ} [NeZero s] (d : ℕ) (S : Finset (Digit p)) :
    ((p : ℤ) ^ s - 1) ∣ digitValue p (shiftDigits d S) ↔
      ((p : ℤ) ^ s - 1) ∣ digitValue p S := by
  rw [digitValue_shiftDigits]
  exact ⟨(isCoprime_modulus_pow p s d (NeZero.pos s)).dvd_of_dvd_mul_right,
    fun h => dvd_mul_of_dvd_left h _⟩

/-- Exponent shifts rotate the residue-content vector. -/
theorem tokenContent_shiftDigits {p s : ℕ} (d : ℕ) (S : Finset (Digit p)) (h : ZMod s) :
    tokenContent (fun t : Digit p => (t.1 : ZMod s)) (shiftDigits d S) h =
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) S (h - d) := by
  have hf : (shiftDigits d S).filter (fun t => (t.1 : ZMod s) = h) =
      (S.filter fun t => (t.1 : ZMod s) = h - d).image (shiftDigit d) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp (mem_filter.mp hx).1
      have he := (mem_filter.mp hx).2
      change ((y.1 + d : ℕ) : ZMod s) = h at he
      rw [Nat.cast_add] at he
      exact mem_image.mpr ⟨y, mem_filter.mpr ⟨hy, eq_sub_iff_add_eq.mpr he⟩, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      refine mem_filter.mpr ⟨mem_image.mpr ⟨y, (mem_filter.mp hy).1, rfl⟩, ?_⟩
      change ((y.1 + d : ℕ) : ZMod s) = h
      rw [Nat.cast_add]
      exact eq_sub_iff_add_eq.mp (mem_filter.mp hy).2
  simp only [tokenContent, hf, card_image_of_injective _ (shiftDigit_injective d)]

theorem inverseContent_translate {s : ℕ} (p : ℚ) (u : ZMod s → ℚ) (d h : ZMod s) :
    inverseContent p (fun j => u (j - d)) h = inverseContent p u (h - d) := by
  unfold inverseContent cyclicWeighted
  congr 1
  apply sum_congr rfl
  intro k _
  change p ^ k * u (h + (k : ZMod s) - d) = p ^ k * u (h - d + k)
  rw [show h + (k : ZMod s) - d = h - d + k by ring]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.dvd_digitValue_shiftDigits_iff
