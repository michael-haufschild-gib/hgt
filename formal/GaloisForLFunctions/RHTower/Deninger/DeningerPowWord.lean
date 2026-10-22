import GaloisForLFunctions.RHTower.Deninger.DeningerConjSplit

/-!
# The normal word of a power

Combining the splitting of a conjugated power with the concatenation statement, the normal word of
`x^{k+1}` is the conjugator, followed by `k` copies of the cyclically reduced part, followed by the
tail.

* `deningerNormalWord_pow` : the normal word of a power.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **The normal word of a power.**  If `x = c v c⁻¹` with `v` cyclically reduced and the left
junction does not cancel, and `B` is the word of `v c⁻¹`, then the normal word of `x^{k+1}` is
`C` followed by `k` copies of `V` followed by `B`. -/
theorem deningerNormalWord_pow (x : PushoutI φ) (C V B : List (Σ i, G i)) (k : ℕ) (hk : 0 < k)
    (hVne : V ≠ [])
    (hCset : ∀ p ∈ C, p.2 ∈ d.set p.1) (hCred : ∀ p ∈ C, p.2 ∉ (φ p.1).range)
    (hCalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) C)
    (hVset : ∀ p ∈ V, p.2 ∈ d.set p.1) (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1)
    (hBset : ∀ p ∈ B, p.2 ∈ d.set p.1) (hBred : ∀ p ∈ B, p.2 ∉ (φ p.1).range)
    (hBalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) B)
    (hCV : ∀ p ∈ C.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1)
    (hVB : ∀ p ∈ V.getLast?, ∀ q ∈ B.head?, p.1 ≠ q.1)
    (hx : x = deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) V *
      (deningerLetterProd (φ := φ) C)⁻¹)
    (hB : deningerLetterProd (φ := φ) B =
      deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹) :
    ((x ^ (k + 1)) • (NormalWord.empty : NormalWord d)).toList =
      C ++ (deningerFlatten (G := G) V k ++ B) := by
  have hsplit : x ^ (k + 1) = deningerLetterProd (φ := φ) C *
      (deningerLetterProd (φ := φ) V) ^ k * deningerLetterProd (φ := φ) B := by
    rw [hx, deningerConj_pow_split, hB]
  rw [hsplit]
  exact deningerNormalWord_conj_pow C V B k hk hVne hCset hCred hCalt hVset hVred hValt hVcyc
    hBset hBred hBalt hCV hVB

end RHTower
