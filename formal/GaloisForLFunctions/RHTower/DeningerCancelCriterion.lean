import GaloisForLFunctions.RHTower.DeningerLeadLetter

/-!
# When a product cancels

The word length of a product of a reduced alternating word with an element is the sum of the two
lengths exactly when the element's normal form does not begin in the factor of the last letter.

* `deningerLen_mul_lt_of_fstIdx` : cancellation when the factors meet.
* `deningerLen_mul_eq_iff` : the criterion.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- If the element begins in the factor of the last letter, the product is strictly shorter than
the sum of the lengths. -/
theorem deningerLen_mul_lt_of_fstIdx (L' : List (Σ i, G i)) (i : ι) (y : G i) (b : PushoutI φ)
    (hb : ((b • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx = some i) :
    deningerLen d (deningerLetterProd (φ := φ) (L' ++ [(⟨i, y⟩ : Σ i, G i)]) * b) <
      (L' ++ [(⟨i, y⟩ : Σ i, G i)]).length + deningerLen d b := by
  have hsplit : deningerLetterProd (φ := φ) (L' ++ [(⟨i, y⟩ : Σ i, G i)]) * b =
      deningerLetterProd (φ := φ) L' * (PushoutI.of i y * b) := by
    rw [deningerLetterProd_snoc, mul_assoc]
  have h1 := deningerLen_letterProd_mul_le (d := d) L' (PushoutI.of i y * b)
  have h2 := deningerLen_of_mul_le_of_fstIdx (d := d) i y b hb
  have h3 : (L' ++ [(⟨i, y⟩ : Σ i, G i)]).length = L'.length + 1 := by simp
  rw [hsplit]
  omega

/-- **The cancellation criterion.** -/
theorem deningerLen_mul_eq_iff (L : List (Σ i, G i)) (b : PushoutI φ)
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L) :
    deningerLen d (deningerLetterProd (φ := φ) L * b) = L.length + deningerLen d b ↔
      ∀ p ∈ L.getLast?, ((b • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠
        some p.1 := by
  constructor
  · intro heq p hp hc
    rw [Option.mem_def] at hp
    obtain ⟨L', hL'⟩ : ∃ L', L = L' ++ [p] :=
      ⟨L.dropLast, (List.dropLast_append_getLast? _ hp).symm⟩
    subst hL'
    have hlt := deningerLen_mul_lt_of_fstIdx (d := d) L' p.1 p.2 b hc
    simp only [Sigma.eta] at hlt
    omega
  · intro hlast
    exact (deningerLen_prepend (d := d) L b hred halt hlast).1

end RHTower
