import GaloisForLFunctions.RHTower.DeningerConjWord
import GaloisForLFunctions.RHTower.DeningerFlattenDrop

/-!
# Equal powers of cyclically reduced words

A power of a cyclically reduced transversal word is normal on the nose: its normal word is the
concatenation of that many copies.  So two cyclically reduced transversal words of the same length
with the same positive power are the same word — a concatenation of copies determines the word it
repeats.

* `deningerNormalWord_cycRed_pow` : the normal word of a power.
* `deningerCycRed_pow_inj` : equal powers of cyclically reduced words of equal length are equal.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **The normal word of a power of a cyclically reduced transversal word** is the concatenation of
that many copies. -/
theorem deningerNormalWord_cycRed_pow (U : List (Σ i, G i)) (k : ℕ) (hk : 0 < k)
    (hUne : U ≠ [])
    (hUset : ∀ p ∈ U, p.2 ∈ d.set p.1) (hUred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (hUalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hUcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1) :
    (((deningerLetterProd (φ := φ) U) ^ k) • (NormalWord.empty : NormalWord d)).toList =
      deningerFlatten (G := G) U k := by
  have h := deningerNormalWord_conj_pow (d := d) [] U [] k hk hUne
    (by simp) (by simp) (by simp) hUset hUred hUalt hUcyc (by simp) (by simp) (by simp)
    (by simp) (by simp)
  simpa using h

/-- **Two cyclically reduced transversal words of the same length with the same positive power are
the same word.** -/
theorem deningerCycRed_pow_inj (U W : List (Σ i, G i)) (k : ℕ) (hk : 0 < k)
    (hUne : U ≠ [])
    (hUset : ∀ p ∈ U, p.2 ∈ d.set p.1) (hUred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (hUalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hUcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1)
    (hWne : W ≠ [])
    (hWset : ∀ p ∈ W, p.2 ∈ d.set p.1) (hWred : ∀ p ∈ W, p.2 ∉ (φ p.1).range)
    (hWalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W)
    (hWcyc : ∀ p ∈ W.getLast?, ∀ q ∈ W.head?, p.1 ≠ q.1)
    (hlen : U.length = W.length)
    (h : (deningerLetterProd (φ := φ) U) ^ k = (deningerLetterProd (φ := φ) W) ^ k) :
    U = W := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  have hflat : deningerFlatten (G := G) U (K + 1) = deningerFlatten (G := G) W (K + 1) := by
    rw [← deningerNormalWord_cycRed_pow (d := d) U (K + 1) hk hUne hUset hUred hUalt hUcyc,
      ← deningerNormalWord_cycRed_pow (d := d) W (K + 1) hk hWne hWset hWred hWalt hWcyc, h]
  exact deningerFlatten_inj U W K hflat hlen

end RHTower
