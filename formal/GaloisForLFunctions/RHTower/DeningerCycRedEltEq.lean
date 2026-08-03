import GaloisForLFunctions.RHTower.DeningerBaseHeadEq
import GaloisForLFunctions.RHTower.DeningerBaseConjWord

/-!
# Uniqueness of roots for cyclically reduced words

A cyclically reduced word is a base group element times a cyclically reduced transversal word, its
letters being replaced by their transversal representatives at the cost of a base element which
accumulates at the front.  Uniqueness of roots for the transversal case therefore gives it for all
cyclically reduced words.

* `deningerCycRed_transversal_form` : the transversal form of a cyclically reduced word.
* `deningerCycRedWord_pow_eq` : equal powers of cyclically reduced words are equal.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
include d in
/-- **The transversal form of a cyclically reduced word.** -/
theorem deningerCycRed_transversal_form (V : List (Σ i, G i)) (hVne : V ≠ [])
    (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) :
    ∃ (h : H) (M : List (Σ i, G i)), M.length = V.length ∧ M ≠ [] ∧
      (∀ p ∈ M, p.2 ∈ d.set p.1) ∧ (∀ p ∈ M, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M ∧
      (∀ p ∈ M.getLast?, ∀ q ∈ M.head?, p.1 ≠ q.1) ∧
      deningerLetterProd (φ := φ) V = PushoutI.base φ h * deningerLetterProd (φ := φ) M := by
  obtain ⟨h, M, hmap, hset, hred, heq⟩ := deningerExists_transversal_form (d := d) V hVred
  have hlen : M.length = V.length := by
    have := congrArg List.length hmap
    simpa using this
  refine ⟨h, M, hlen, ?_, hset, hred, deningerIsChain_of_map_fst V M hmap hValt,
    deningerCyc_of_map_fst V M hmap hVcyc, heq⟩
  intro hnil
  rw [hnil] at hlen
  exact hVne (List.length_eq_zero_iff.1 (by simpa using hlen.symm))

include d in
/-- **Equal powers of cyclically reduced words are equal.** -/
theorem deningerCycRedWord_pow_eq (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (hcomm : ∀ u v : H, u * v = v * u)
    (htf : ∀ (u : H) (n : ℕ), 0 < n → u ^ n = 1 → u = 1)
    (U W : List (Σ i, G i)) (hUne : U ≠ [])
    (hUred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (hUalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hUcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1)
    (hWne : W ≠ [])
    (hWred : ∀ p ∈ W, p.2 ∉ (φ p.1).range)
    (hWalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W)
    (hWcyc : ∀ p ∈ W.getLast?, ∀ q ∈ W.head?, p.1 ≠ q.1)
    (hlen : U.length = W.length) (n : ℕ)
    (heq : (deningerLetterProd (φ := φ) U) ^ (n + 1) =
      (deningerLetterProd (φ := φ) W) ^ (n + 1)) :
    deningerLetterProd (φ := φ) U = deningerLetterProd (φ := φ) W := by
  obtain ⟨j, M, hMlen, hMne, hMset, hMred, hMalt, hMcyc, hUeq⟩ :=
    deningerCycRed_transversal_form (d := d) U hUne hUred hUalt hUcyc
  obtain ⟨k, M', hM'len, hM'ne, hM'set, hM'red, hM'alt, hM'cyc, hWeq⟩ :=
    deningerCycRed_transversal_form (d := d) W hWne hWred hWalt hWcyc
  have hMM : M.length = M'.length := by rw [hMlen, hM'len, hlen]
  rw [hUeq, hWeq] at heq
  have hwords : M = M' :=
    deningerBaseHead_pow_word_eq (d := d) M M' j k n hMne hMset hMred hMalt hMcyc
      hM'ne hM'set hM'red hM'alt hM'cyc hMM heq
  subst hwords
  rw [hUeq, hWeq]
  exact deningerBaseHead_pow_eq (d := d) hφ hcent hcomm htf M hMne hMset hMred hMalt hMcyc
    j k n heq

end RHTower
