import GaloisForLFunctions.RHTower.DeningerCycStepCases

/-!
# The cyclic reduction data

The data extracted from an element by cyclic reduction is a splitting of its word into a conjugator
and a tail, together with the cyclically reduced part.  The two descriptions of the element — as a
conjugate, and through the tail — are equivalent, so the tail is literally the suffix of the word
after the conjugator.

* `deningerCycData_iff` : the two descriptions agree.
* `deningerCycData_base` : the data of an already cyclically reduced word.
* `deningerCycData_step` : the data is inherited by a conjugation step.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **The two descriptions agree.**  Writing the element as a conjugate is the same as identifying
the tail of its word with the cyclically reduced part times the inverse conjugator. -/
theorem deningerCycData_iff (C R V : List (Σ i, G i)) :
    deningerLetterProd (φ := φ) (C ++ R) =
        deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) V *
          (deningerLetterProd (φ := φ) C)⁻¹ ↔
      deningerLetterProd (φ := φ) R =
        deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹ := by
  rw [deningerLetterProd_append, mul_assoc]
  exact mul_right_inj _

/-- **The data of an already cyclically reduced word.** -/
theorem deningerCycData_base (L : List (Σ i, G i)) :
    deningerLetterProd (φ := φ) ([] ++ L) =
      deningerLetterProd (φ := φ) [] * deningerLetterProd (φ := φ) L *
        (deningerLetterProd (φ := φ) [])⁻¹ := by
  rw [deningerLetterProd_nil]
  simp

/-- **The data is inherited by a conjugation step.**  Prepending a letter to the conjugator
corresponds to multiplying the tail by the inverse of that letter. -/
theorem deningerCycData_step (q : Σ i, G i) (C₁ V R₁ R : List (Σ i, G i))
    (hIH : deningerLetterProd (φ := φ) R₁ =
      deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C₁)⁻¹)
    (hR : deningerLetterProd (φ := φ) R =
      deningerLetterProd (φ := φ) R₁ * (PushoutI.of q.1 q.2)⁻¹) :
    deningerLetterProd (φ := φ) R =
      deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) (q :: C₁))⁻¹ := by
  rw [hR, hIH, deningerLetterProd_cons, mul_inv_rev, mul_assoc]

end RHTower
