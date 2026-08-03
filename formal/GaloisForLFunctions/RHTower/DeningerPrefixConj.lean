import GaloisForLFunctions.RHTower.DeningerLeadSurvives

/-!
# The conjugator is a prefix

In an amalgam the conjugator produced by cyclic reduction is a prefix of the word of the element,
so cancelling it off leaves the corresponding suffix.  The right hand junction of the power word
then comes from the alternation of the original word rather than from any length inequality: the
last letter of the cyclically reduced part carries the index of the last stripped letter.

* `deningerLetterProd_prefix_cancel` : cancelling a prefix.
* `deningerJunction_of_append` : the junction from alternation.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- Cancelling a prefix off a word leaves the suffix. -/
theorem deningerLetterProd_prefix_cancel (C B : List (Σ i, G i)) :
    (deningerLetterProd (φ := φ) C)⁻¹ * deningerLetterProd (φ := φ) (C ++ B) =
      deningerLetterProd (φ := φ) B := by
  rw [deningerLetterProd_append, ← mul_assoc, inv_mul_cancel, one_mul]

omit [∀ i, Group (G i)] in
/-- **The junction from alternation.**  If the last letter of the cyclically reduced part carries
the index of the last letter of the conjugator, then it differs from the first letter of the
tail. -/
theorem deningerJunction_of_append (C B V : List (Σ i, G i)) (hCne : C ≠ [])
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (C ++ B))
    (hlast : ∀ p ∈ V.getLast?, ∀ q ∈ C.getLast?, p.1 = q.1) :
    ∀ p ∈ V.getLast?, ∀ q ∈ B.head?, p.1 ≠ q.1 := by
  intro p hp q hq
  obtain ⟨c, hc⟩ : ∃ c, C.getLast? = some c := by
    cases hC : C.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hC) hCne
    | some c => exact ⟨c, rfl⟩
  have hpc : p.1 = c.1 := hlast p hp c (by rw [hc]; rfl)
  rw [hpc]
  exact (List.isChain_append.1 halt).2.2 c (by rw [hc]; rfl) q hq

end RHTower
