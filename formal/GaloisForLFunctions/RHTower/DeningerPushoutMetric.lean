import GaloisForLFunctions.RHTower.DeningerPushoutRoot

/-!
# The word length is subadditive

The word length of a product is at most the sum of the word lengths, and hence conjugation changes
the word length by at most twice the length of the conjugator.

* `deningerLen_mul_le` : subadditivity.
* `deningerLen_le_mul` : the reverse triangle inequality.
* `deningerLen_conj_ge` : the effect of conjugation.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

theorem deningerLen_letterProd_mul_le (L : List (Σ i, G i)) (z : PushoutI φ) :
    deningerLen d (deningerLetterProd (φ := φ) L * z) ≤ L.length + deningerLen d z := by
  induction L with
  | nil => simp [deningerLetterProd_nil]
  | cons p L' ih =>
    rw [deningerLetterProd_cons, mul_assoc]
    have hstep := deningerLen_of_mul_le (d := d) p.1 p.2 (deningerLetterProd (φ := φ) L' * z)
    have hlen : (p :: L').length = L'.length + 1 := by simp
    omega

/-- **Subadditivity of the word length.** -/
theorem deningerLen_mul_le (g z : PushoutI φ) :
    deningerLen d (g * z) ≤ deningerLen d g + deningerLen d z := by
  rcases deningerExists_letterProd (d := d) g with ⟨h₀, hg, h0⟩ | ⟨L, _, _, _, hlen, hg⟩
  · rw [hg, deningerLen_base_mul]
    omega
  · rw [hg] at hlen ⊢
    have := deningerLen_letterProd_mul_le (d := d) L z
    omega

/-- The reverse triangle inequality. -/
theorem deningerLen_le_mul (g z : PushoutI φ) :
    deningerLen d g ≤ deningerLen d (g * z) + deningerLen d z := by
  have hb := deningerLen_mul_le (d := d) (g * z) z⁻¹
  rw [mul_assoc, mul_inv_cancel, mul_one, deningerLen_inv] at hb
  exact hb

/-- **Conjugation changes the word length by at most twice the length of the conjugator.** -/
theorem deningerLen_conj_ge (c g : PushoutI φ) :
    deningerLen d g ≤ deningerLen d (c⁻¹ * g * c) + 2 * deningerLen d c := by
  have h1 := deningerLen_le_mul (d := d) (c⁻¹ * g) c
  have h2 : deningerLen d (c⁻¹ * g) ≤ deningerLen d c⁻¹ + deningerLen d g := by
    exact deningerLen_mul_le (d := d) c⁻¹ g
  have h3 := deningerLen_le_mul (d := d) g c
  have h4 : deningerLen d g ≤ deningerLen d c + deningerLen d (c⁻¹ * g) := by
    have := deningerLen_mul_le (d := d) c (c⁻¹ * g)
    rw [← mul_assoc, mul_inv_cancel, one_mul] at this
    exact this
  have h5 : deningerLen d c⁻¹ = deningerLen d c := deningerLen_inv (d := d) c
  omega

theorem deningerLen_conj_le (c g : PushoutI φ) :
    deningerLen d (c⁻¹ * g * c) ≤ deningerLen d g + 2 * deningerLen d c := by
  have h1 := deningerLen_mul_le (d := d) (c⁻¹ * g) c
  have h2 := deningerLen_mul_le (d := d) c⁻¹ g
  have h5 : deningerLen d c⁻¹ = deningerLen d c := deningerLen_inv (d := d) c
  omega

end RHTower
