import GaloisForLFunctions.RHTower.Deninger.DeningerConjTrichotomy

/-!
# Conjugating a word that cancels at neither end

If the last letter of the conjugating word lies in a factor which occurs at neither end of the word
being conjugated, nothing cancels anywhere and the length is the full sum.

* `deningerLen_conj_word` : the length of such a conjugate.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Conjugating by a word that cancels at neither end.**  The conjugate has the length of the
conjugating word twice over, plus the length of the word conjugated. -/
theorem deningerLen_conj_word (A V : List (Σ i, G i))
    (hAred : ∀ p ∈ A, p.2 ∉ (φ p.1).range)
    (hAalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) A)
    (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hVne : V ≠ [])
    (hAV : ∀ p ∈ A.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1)
    (hVA : ∀ p ∈ V.getLast?, ∀ q ∈ A.getLast?, p.1 ≠ q.1) :
    deningerLen d (deningerLetterProd (φ := φ) A * deningerLetterProd (φ := φ) V *
      (deningerLetterProd (φ := φ) A)⁻¹) = 2 * A.length + V.length := by
  set B : List (Σ i, G i) := deningerInvList (G := G) A with hB
  set W : List (Σ i, G i) := A ++ (V ++ B) with hW
  have hBhead : B.head?.map Sigma.fst = A.getLast?.map Sigma.fst :=
    deningerInvList_head_fst (G := G) A
  have hprod : deningerLetterProd (φ := φ) W =
      deningerLetterProd (φ := φ) A * deningerLetterProd (φ := φ) V *
        (deningerLetterProd (φ := φ) A)⁻¹ := by
    rw [hW, deningerLetterProd_append, deningerLetterProd_append, hB,
      ← deningerLetterProd_inv, ← mul_assoc]
  have hWred : ∀ p ∈ W, p.2 ∉ (φ p.1).range := by
    intro p hp
    rw [hW] at hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hAred p hp
    · rcases List.mem_append.1 hp with hp | hp
      · exact hVred p hp
      · exact deningerInvList_reduced (G := G) A hAred p hp
  have hVB : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (V ++ B) := by
    refine List.isChain_append.2 ⟨hValt, deningerInvList_isChain (G := G) A hAalt,
      fun p hp q hq => ?_⟩
    rw [Option.mem_def] at hq
    have h1 : B.head?.map Sigma.fst = some q.1 := by rw [hq]; rfl
    rw [hBhead] at h1
    cases hA : A.getLast? with
    | none => rw [hA] at h1; simp at h1
    | some a =>
      rw [hA] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [← h1]
      exact hVA p hp a hA
  have hWalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W := by
    rw [hW]
    refine List.isChain_append.2 ⟨hAalt, hVB, fun p hp q hq => ?_⟩
    rw [List.head?_append_of_ne_nil _ hVne] at hq
    exact hAV p hp q hq
  have hlen := congrArg List.length (deningerNormalWord_map_fst (d := d) W hWred hWalt)
  rw [List.length_map, List.length_map] at hlen
  show ((_ • (NormalWord.empty : NormalWord d)) : NormalWord d).toList.length = _
  rw [← hprod, hlen, hW]
  simp only [List.length_append, hB, deningerInvList_length]
  ring

end RHTower
