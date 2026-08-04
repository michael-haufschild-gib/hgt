import GaloisForLFunctions.RHTower.DeningerCycRedEltEq
import GaloisForLFunctions.RHTower.DeningerBaseHeadPow

/-!
# A power of a cyclically reduced word is cyclically reduced

The block form of a power of a base element times a cyclically reduced transversal word gives a word
whose first and last letters are those of the original, so the cyclic condition survives; absorbing
the base element into the first letter turns it into a word product.  The length multiplies by the
exponent.

* `deningerCycRed_pow_word` : the power, as a cyclically reduced word.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
include d in
/-- **A power of a cyclically reduced word is a cyclically reduced word** of the multiplied
length. -/
theorem deningerCycRed_pow_word (V : List (Σ i, G i)) (hVne : V ≠ [])
    (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) (k : ℕ) :
    ∃ W : List (Σ i, G i), W.length = (k + 1) * V.length ∧ W ≠ [] ∧
      (∀ p ∈ W, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W ∧
      (∀ p ∈ W.getLast?, ∀ q ∈ W.head?, p.1 ≠ q.1) ∧
      (deningerLetterProd (φ := φ) V) ^ (k + 1) = deningerLetterProd (φ := φ) W := by
  classical
  obtain ⟨h, M, hMlen, hMne, hMset, hMred, hMalt, hMcyc, hVeq⟩ :=
    deningerCycRed_transversal_form (d := d) V hVne hVred hValt hVcyc
  obtain ⟨h', N, hNlen, hNset, hNred, hNalt, hNhead, hpow⟩ :=
    deningerBaseHead_pow_word (d := d) M hMne hMset hMred hMalt hMcyc h k
  have hNMne : N ++ M ≠ [] := List.append_ne_nil_of_right_ne_nil N hMne
  have hNMcyc : ∀ p ∈ (N ++ M).getLast?, ∀ q ∈ (N ++ M).head?, p.1 ≠ q.1 := by
    intro p hp q hq
    rw [List.getLast?_append_of_ne_nil _ hMne] at hp
    exact deningerCyc_of_map_fst_cross M M (N ++ M) rfl hNhead hMcyc p hp q hq
  refine ⟨deningerAbsorb φ h' (N ++ M), ?_, deningerAbsorb_ne_nil h' _ hNMne,
    deningerAbsorb_reduced h' _ hNred, deningerAbsorb_isChain h' _ hNalt,
    deningerCyc_of_map_fst (N ++ M) _ (deningerAbsorb_map_fst h' (N ++ M)) hNMcyc, ?_⟩
  · rw [deningerAbsorb_length, List.length_append, hNlen, hMlen]
    ring
  · rw [hVeq, hpow, deningerBase_mul_letterProd h' (N ++ M) hNMne]

end RHTower
