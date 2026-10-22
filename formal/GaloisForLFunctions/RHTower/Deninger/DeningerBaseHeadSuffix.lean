import GaloisForLFunctions.RHTower.Deninger.DeningerBaseHeadPow
import GaloisForLFunctions.RHTower.Deninger.DeningerWordIndices

/-!
# Equal powers of cyclically reduced elements have the same word

An element of an amalgam whose normal word is cyclically reduced is a base group element times a
cyclically reduced transversal word, and that word is read off its normal form, so it is determined
by the element.  The last block of a power is the word itself, so two such elements of the same
length with the same positive power carry the same word — only their base heads can still differ.

* `deningerBaseWord_eq` : the word of a base element times a transversal word is determined.
* `deningerBaseWord_head_eq` : the head is determined as well.
* `deningerBaseHead_pow_word_eq` : equal powers force equal words.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The word of a base element times a transversal word is determined by the product.** -/
theorem deningerBaseWord_eq (h h' : H) (L L' : List (Σ i, G i))
    (hset : ∀ p ∈ L, p.2 ∈ d.set p.1) (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hset' : ∀ p ∈ L', p.2 ∈ d.set p.1) (hred' : ∀ p ∈ L', p.2 ∉ (φ p.1).range)
    (halt' : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L')
    (heq : PushoutI.base φ h * deningerLetterProd (φ := φ) L =
      PushoutI.base φ h' * deningerLetterProd (φ := φ) L') :
    L = L' := by
  have e1 : (((PushoutI.base φ h * deningerLetterProd (φ := φ) L) •
      (NormalWord.empty : NormalWord d)) : NormalWord d).toList = L := by
    rw [deningerNormalWord_base_mul]
    exact (deningerNormalWord_letterProd L hset hred halt).1
  have e2 : (((PushoutI.base φ h' * deningerLetterProd (φ := φ) L') •
      (NormalWord.empty : NormalWord d)) : NormalWord d).toList = L' := by
    rw [deningerNormalWord_base_mul]
    exact (deningerNormalWord_letterProd L' hset' hred' halt').1
  rw [heq, e2] at e1
  exact e1.symm

include d in
/-- **The head is determined as well.** -/
theorem deningerBaseWord_head_eq (hφ : ∀ i, Function.Injective (φ i)) (h h' : H)
    (L L' : List (Σ i, G i))
    (hset : ∀ p ∈ L, p.2 ∈ d.set p.1) (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hset' : ∀ p ∈ L', p.2 ∈ d.set p.1) (hred' : ∀ p ∈ L', p.2 ∉ (φ p.1).range)
    (halt' : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L')
    (heq : PushoutI.base φ h * deningerLetterProd (φ := φ) L =
      PushoutI.base φ h' * deningerLetterProd (φ := φ) L') :
    h = h' ∧ L = L' := by
  have hL : L = L' :=
    deningerBaseWord_eq (d := d) h h' L L' hset hred halt hset' hred' halt' heq
  subst hL
  refine ⟨PushoutI.base_injective hφ (mul_right_cancel heq), rfl⟩

include d in
/-- **Equal powers force equal words.**  Two base group elements times cyclically reduced
transversal words of the same length whose positive powers agree carry the same word. -/
theorem deningerBaseHead_pow_word_eq (M W : List (Σ i, G i)) (j k : H) (n : ℕ)
    (hMne : M ≠ [])
    (hMset : ∀ p ∈ M, p.2 ∈ d.set p.1) (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (hMcyc : ∀ p ∈ M.getLast?, ∀ q ∈ M.head?, p.1 ≠ q.1)
    (hWne : W ≠ [])
    (hWset : ∀ p ∈ W, p.2 ∈ d.set p.1) (hWred : ∀ p ∈ W, p.2 ∉ (φ p.1).range)
    (hWalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W)
    (hWcyc : ∀ p ∈ W.getLast?, ∀ q ∈ W.head?, p.1 ≠ q.1)
    (hlen : M.length = W.length)
    (heq : (PushoutI.base φ j * deningerLetterProd (φ := φ) M) ^ (n + 1) =
      (PushoutI.base φ k * deningerLetterProd (φ := φ) W) ^ (n + 1)) :
    M = W := by
  obtain ⟨h, N, hNlen, hNset, hNred, hNalt, -, hNeq⟩ :=
    deningerBaseHead_pow_word (d := d) M hMne hMset hMred hMalt hMcyc j n
  obtain ⟨h', N', hN'len, hN'set, hN'red, hN'alt, -, hN'eq⟩ :=
    deningerBaseHead_pow_word (d := d) W hWne hWset hWred hWalt hWcyc k n
  have hwords : N ++ M = N' ++ W := by
    refine deningerBaseWord_eq (d := d) h h' _ _ hNset hNred hNalt hN'set hN'red hN'alt ?_
    rw [← hNeq, ← hN'eq, heq]
  refine List.append_inj_right hwords ?_
  rw [hNlen, hN'len, hlen]

end RHTower
