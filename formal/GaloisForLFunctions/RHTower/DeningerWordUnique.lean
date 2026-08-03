import GaloisForLFunctions.RHTower.DeningerConjPowCycRed

/-!
# Two words with the same product

Reduced alternating words are not determined by their products — the letters can be shifted by the
base group — but their sequences of factors are, since that sequence is read off the normal form.

* `deningerWords_map_fst_eq` : two reduced alternating words with the same product run through the
  same factors.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Two reduced alternating words with the same product run through the same factors.** -/
theorem deningerWords_map_fst_eq (L M : List (Σ i, G i))
    (hLred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (hLalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (h : deningerLetterProd (φ := φ) L = deningerLetterProd (φ := φ) M) :
    L.map Sigma.fst = M.map Sigma.fst := by
  rw [← deningerNormalWord_map_fst (d := d) L hLred hLalt,
    ← deningerNormalWord_map_fst (d := d) M hMred hMalt, h]

include d in
/-- Two reduced alternating words with the same product have the same length. -/
theorem deningerWords_length_eq (L M : List (Σ i, G i))
    (hLred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (hLalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (h : deningerLetterProd (φ := φ) L = deningerLetterProd (φ := φ) M) :
    L.length = M.length := by
  have := congrArg List.length
    (deningerWords_map_fst_eq (d := d) L M hLred hLalt hMred hMalt h)
  simpa using this

end RHTower
