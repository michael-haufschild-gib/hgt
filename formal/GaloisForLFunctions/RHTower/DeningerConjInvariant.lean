import GaloisForLFunctions.RHTower.DeningerConjLetterForm

/-!
# The conjugator invariant

A conjugating element built up by cancelling letters is a base group element times an inverted word.
Cancelling one more letter at the front keeps that shape: the new letter joins the inverted word,
and the base group elements absorb into it.

* `deningerConjInvariant_front` : the invariant is preserved by a front cancellation.
* `deningerConjInvariant_back` : and by a back cancellation, which shortens the word instead.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **A front cancellation preserves the conjugator invariant.**  If the conjugator so far is a base
group element times an inverted word, then after cancelling the front letter it is again of that
shape, with one more letter in the word. -/
theorem deningerConjInvariant_front (A' P : List (Σ i, G i)) (m₀ m₁ k : H) (i : ι) (x u₁ : G i)
    (hIH : deningerLetterProd (φ := φ) A' * PushoutI.base φ m₀ =
      PushoutI.base φ m₁ * (deningerLetterProd (φ := φ) P)⁻¹)
    (hk : x * u₁ = φ i k) :
    deningerLetterProd (φ := φ) (A' ++ [(⟨i, x⟩ : Σ i, G i)]) =
      PushoutI.base φ m₁ *
        (deningerLetterProd (φ := φ)
          ((⟨i, u₁ * (φ i (m₀⁻¹ * k))⁻¹⟩ : Σ i, G i) :: P))⁻¹ := by
  have hA' : deningerLetterProd (φ := φ) A' =
      PushoutI.base φ m₁ * (deningerLetterProd (φ := φ) P)⁻¹ * (PushoutI.base φ m₀)⁻¹ := by
    rw [← hIH]
    group
  rw [deningerLetterProd_snoc, hA', deningerConjLetter_front i x u₁ k hk,
    deningerLetterProd_cons, mul_inv_rev]
  have hbase : (PushoutI.base φ m₀)⁻¹ * PushoutI.base φ k = PushoutI.base φ (m₀⁻¹ * k) := by
    rw [map_mul, map_inv]
  rw [show PushoutI.base φ m₁ * (deningerLetterProd (φ := φ) P)⁻¹ * (PushoutI.base φ m₀)⁻¹ *
      (PushoutI.base φ k * (PushoutI.of (φ := φ) i u₁)⁻¹) =
    PushoutI.base φ m₁ * (deningerLetterProd (φ := φ) P)⁻¹ *
      ((PushoutI.base φ m₀)⁻¹ * PushoutI.base φ k * (PushoutI.of (φ := φ) i u₁)⁻¹) by group,
    hbase, deningerBase_mul_inv_of]
  group

/-- **A back cancellation preserves the conjugator invariant, shortening the word.**  The letter
cancelled at the back meets the first letter of the inverted word, and the two combine into the base
group, which is then carried along. -/
theorem deningerConjInvariant_back (A' P' : List (Σ i, G i)) (m₀ m₁ k n : H) (i : ι)
    (x uℓ y : G i)
    (hIH : deningerLetterProd (φ := φ) A' * PushoutI.base φ m₀ =
      PushoutI.base φ m₁ *
        (deningerLetterProd (φ := φ) ((⟨i, y⟩ : Σ i, G i) :: P'))⁻¹)
    (hk : uℓ * x⁻¹ = φ i k)
    (hcancel : y⁻¹ * (φ i (m₀⁻¹ * k⁻¹)) * uℓ = φ i n) :
    deningerLetterProd (φ := φ) (A' ++ [(⟨i, x⟩ : Σ i, G i)]) * PushoutI.base φ n⁻¹ =
      PushoutI.base φ m₁ * (deningerLetterProd (φ := φ) P')⁻¹ := by
  have hA' : deningerLetterProd (φ := φ) A' =
      PushoutI.base φ m₁ *
        (deningerLetterProd (φ := φ) ((⟨i, y⟩ : Σ i, G i) :: P'))⁻¹ *
        (PushoutI.base φ m₀)⁻¹ := by
    rw [← hIH]
    group
  have hthree : (PushoutI.of (φ := φ) i y)⁻¹ * PushoutI.base φ (m₀⁻¹ * k⁻¹) *
      PushoutI.of (φ := φ) i uℓ = PushoutI.base φ n := by
    rw [← PushoutI.of_apply_eq_base φ i (m₀⁻¹ * k⁻¹), ← PushoutI.of_apply_eq_base φ i n,
      ← hcancel, map_mul, map_mul, map_inv]
    simp only [← map_mul, ← map_inv]
  rw [deningerLetterProd_snoc, hA', deningerConjLetter_back i x uℓ k hk,
    deningerLetterProd_cons, mul_inv_rev]
  rw [show PushoutI.base φ m₁ *
        ((deningerLetterProd (φ := φ) P')⁻¹ * (PushoutI.of (φ := φ) i y)⁻¹) *
        (PushoutI.base φ m₀)⁻¹ *
        ((PushoutI.base φ k)⁻¹ * PushoutI.of (φ := φ) i uℓ) * PushoutI.base φ n⁻¹ =
      PushoutI.base φ m₁ * (deningerLetterProd (φ := φ) P')⁻¹ *
        ((PushoutI.of (φ := φ) i y)⁻¹ *
          ((PushoutI.base φ m₀)⁻¹ * (PushoutI.base φ k)⁻¹) *
          PushoutI.of (φ := φ) i uℓ) * PushoutI.base φ n⁻¹ by group,
    show (PushoutI.base φ m₀)⁻¹ * (PushoutI.base φ k)⁻¹ =
      PushoutI.base φ (m₀⁻¹ * k⁻¹) by rw [map_mul, map_inv, map_inv],
    hthree, map_inv]
  group

end RHTower
