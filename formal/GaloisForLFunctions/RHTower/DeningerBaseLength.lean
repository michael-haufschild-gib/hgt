import GaloisForLFunctions.RHTower.DeningerConjNormalize

/-!
# The base group does not change the word length

Multiplication by the base group on either side, and conjugation by it, leave the word length
unchanged.  On the left this is immediate from the normal form; on the right it follows by
inversion.

* `deningerLen_mul_base` : multiplication on the right.
* `deningerLen_base_conj` : conjugation.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- Multiplication by the base group on the right does not change the word length. -/
theorem deningerLen_mul_base (g : PushoutI φ) (h : H) :
    deningerLen d (g * PushoutI.base φ h) = deningerLen d g := by
  rw [← deningerLen_inv (d := d) (g * PushoutI.base φ h), mul_inv_rev, ← map_inv,
    deningerLen_base_mul, deningerLen_inv]

/-- Conjugation by the base group does not change the word length. -/
theorem deningerLen_base_conj (g : PushoutI φ) (h : H) :
    deningerLen d (PushoutI.base φ h * g * PushoutI.base φ h⁻¹) = deningerLen d g := by
  rw [deningerLen_mul_base, deningerLen_base_mul]

/-- Conjugation by the base group commutes with powers, so the word lengths of the powers agree. -/
theorem deningerLen_base_conj_pow (g : PushoutI φ) (h : H) (m : ℕ) :
    deningerLen d ((PushoutI.base φ h * g * PushoutI.base φ h⁻¹) ^ m) =
      deningerLen d (g ^ m) := by
  have hconj : (PushoutI.base φ h * g * PushoutI.base φ h⁻¹) ^ m =
      PushoutI.base φ h * g ^ m * PushoutI.base φ h⁻¹ := by
    have hmap := map_pow (MulAut.conj (PushoutI.base φ h)) g m
    simp only [MulAut.conj_apply, ← map_inv] at hmap
    exact hmap.symm
  rw [hconj, deningerLen_base_conj]

/-- The word length of a conjugate is unchanged if the conjugator lies in the base group. -/
theorem deningerLen_conj_of_len_zero (c g : PushoutI φ) (hc : deningerLen d c = 0) :
    deningerLen d (c⁻¹ * g * c) = deningerLen d g := by
  obtain ⟨h, hh⟩ := (deningerLen_eq_zero_iff (d := d) c).1 hc
  rw [← hh, ← map_inv, deningerLen_mul_base, deningerLen_base_mul]

end RHTower
