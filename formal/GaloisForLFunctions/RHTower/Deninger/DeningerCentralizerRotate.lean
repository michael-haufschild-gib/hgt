import GaloisForLFunctions.RHTower.Deninger.DeningerConjugacyCriterion
import GaloisForLFunctions.RHTower.Deninger.DeningerRotateCentElt

/-!
# Centralizing a cyclically reduced element rotates its word

An element centralizing a cyclically reduced word of at least two letters conjugates it to itself,
which is no longer than itself, so the conjugacy criterion applies: the word is a rotation of
itself, up to the base group, and the centralizing element is the element realizing that rotation
times a power of the word.  An element of the base group rotates by zero.

* `deningerCent_rotate` : the rotation symmetry and the form of the centralizing element.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **A centralizing element rotates the word.**  If `z` commutes with the product of a cyclically
reduced word of at least two letters, that product is a rotation of itself up to the base group, and
`z` is the element realizing the rotation times a power of the product. -/
theorem deningerCent_rotate (U : List (Σ i, G i)) (hlen2 : 2 ≤ U.length)
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1) (z : PushoutI φ)
    (hz : z⁻¹ * deningerLetterProd (φ := φ) U * z = deningerLetterProd (φ := φ) U) :
    ∃ (t : ℕ) (m : H) (j : ℤ), t ≤ U.length ∧
      deningerLetterProd (φ := φ) U =
        PushoutI.base φ m * deningerLetterProd (φ := φ) (U.rotate t) *
          (PushoutI.base φ m)⁻¹ ∧
      deningerRotateCentElt φ U t m * z⁻¹ = deningerLetterProd (φ := φ) U ^ j := by
  classical
  rcases deningerExists_letterProd (d := d) z⁻¹ with ⟨h₀, hz₀, -⟩ | ⟨A, -, hAred, hAalt, -, hz₀⟩
  · refine ⟨0, h₀, 0, Nat.zero_le _, ?_, ?_⟩
    · have h1 : PushoutI.base φ h₀ = z⁻¹ := hz₀.symm
      rw [List.rotate_zero, h1, inv_inv, hz]
    · rw [deningerRotateCentElt, List.take_zero, deningerLetterProd_nil, one_mul, hz₀,
        zpow_zero, inv_mul_cancel]
  · have hconj : deningerLetterProd (φ := φ) A * deningerLetterProd (φ := φ) U *
        (deningerLetterProd (φ := φ) A)⁻¹ = deningerLetterProd (φ := φ) U := by
      rw [← hz₀, inv_inv]
      exact hz
    obtain ⟨t, m, j, ht, hrot, htr⟩ :=
      deningerConj_cycRed_rotate (d := d) A U hAred hAalt hlen2 hred halt hcyc
        (by rw [hconj, deningerLen_letterProd (d := d) U hred halt])
    refine ⟨t, m, j, ht, by rw [← hconj, hrot], ?_⟩
    rw [deningerRotateCentElt, hz₀]
    exact htr

end RHTower
