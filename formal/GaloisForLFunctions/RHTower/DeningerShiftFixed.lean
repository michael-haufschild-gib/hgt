import GaloisForLFunctions.RHTower.DeningerConjBase

/-!
# The shift preserves differences

Pushing a base element through a word produces a new base element and a new word.  When two base
elements are pushed through the same word and produce the same word, their difference is unchanged:
the difference is conjugated by the word into the difference of the outputs, and conjugation by a
word does not move the base group.

* `deningerShift_diff_fixed` : the difference of the two base elements is preserved.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The shift preserves differences.**  Two base elements pushed through the same word, producing
the same word, keep their difference. -/
theorem deningerShift_diff_fixed (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (M W : List (Σ i, G i))
    (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (a b a' b' : H)
    (h1 : deningerLetterProd (φ := φ) M * PushoutI.base φ a =
      PushoutI.base φ a' * deningerLetterProd (φ := φ) W)
    (h2 : deningerLetterProd (φ := φ) M * PushoutI.base φ b =
      PushoutI.base φ b' * deningerLetterProd (φ := φ) W) :
    a' * b'⁻¹ = a * b⁻¹ := by
  have hd := deningerShift_diff (φ := φ) M W a b a' b' h1 h2
  refine deningerConj_base_eq (d := d) hφ hcent (a * b⁻¹) (a' * b'⁻¹) M hMred hMalt ?_
  rw [← hd]
  group

end RHTower
