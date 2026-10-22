import GaloisForLFunctions.RHTower.Deninger.DeningerCycRecursion

/-!
# The index sequence of a word is an invariant

The normal form of a product of a reduced alternating word has the same sequence of indices as the
word, whether or not the letters lie in the transversal: putting a word into transversal form moves
base group elements leftwards through it, which changes the letters but not their factors.

* `deningerNormalWord_base_mul` : the base group on the left does not change the word.
* `deningerNormalWord_map_fst` : the index sequence is an invariant.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- Multiplying by the base group on the left does not change the word of the normal form. -/
theorem deningerNormalWord_base_mul (h : H) (g : PushoutI φ) :
    (((PushoutI.base φ h * g) • (NormalWord.empty : NormalWord d)) : NormalWord d).toList =
      ((g • (NormalWord.empty : NormalWord d)) : NormalWord d).toList := by
  rw [mul_smul, NormalWord.base_smul_def]

include d in
/-- **The index sequence is an invariant.**  The normal form of a product of a reduced alternating
word has the same indices as the word. -/
theorem deningerNormalWord_map_fst (L : List (Σ i, G i))
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L) :
    (((deningerLetterProd (φ := φ) L) • (NormalWord.empty : NormalWord d)) :
        NormalWord d).toList.map Sigma.fst = L.map Sigma.fst := by
  obtain ⟨h, N, hmap, hset, hredN, heq⟩ := deningerExists_transversal_form (d := d) L hred
  have haltN : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) N :=
    deningerIsChain_of_map_fst L N hmap halt
  rw [heq, deningerNormalWord_base_mul,
    (deningerNormalWord_letterProd (d := d) N hset hredN haltN).1, hmap]

end RHTower
