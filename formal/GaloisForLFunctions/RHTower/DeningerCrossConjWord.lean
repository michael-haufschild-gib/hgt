import GaloisForLFunctions.RHTower.DeningerShortConj

/-!
# Conjugating a factor element by a word starting in another factor

If a conjugator is a reduced word whose first letter lies outside the factor of the element being
conjugated, then no cancellation occurs at either junction and the conjugate is a reduced word of
twice the conjugator plus one letters.  So a conjugator carrying a factor element to a short element
must start in that same factor.

* `deningerInvList_getLast_fst` : the last index of the inverse word.
* `deningerLen_conj_word_letter` : the length of the conjugate.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- The last index of the inverse word is the first index of the word. -/
theorem deningerInvList_getLast_fst (L : List (Σ i, G i)) :
    (deningerInvList (G := G) L).getLast?.map Sigma.fst = L.head?.map Sigma.fst := by
  simp [deningerInvList, List.getLast?_reverse, List.head?_map, Function.comp_def]

include d in
/-- **The length of the conjugate of a factor element by a word starting in another factor.** -/
theorem deningerLen_conj_word_letter (L : List (Σ i, G i))
    (hLred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (hLalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (i : ι) (u : G i) (hu : u ∉ (φ i).range)
    (hhead : ∀ q ∈ L.head?, i ≠ q.1) :
    deningerLen d ((deningerLetterProd (φ := φ) L)⁻¹ * PushoutI.of (φ := φ) i u *
      deningerLetterProd (φ := φ) L) = 2 * L.length + 1 := by
  classical
  set W : List (Σ i, G i) :=
    deningerInvList (G := G) L ++ ((⟨i, u⟩ : Σ i, G i) :: L) with hW
  have hred : ∀ p ∈ W, p.2 ∉ (φ p.1).range := by
    intro p hp
    rw [hW] at hp
    rcases List.mem_append.1 hp with hp | hp
    · exact deningerInvList_reduced L hLred p hp
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact hu
      · exact hLred p hp
  have hconsalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) ((⟨i, u⟩ : Σ i, G i) :: L) :=
    List.isChain_cons.2 ⟨hhead, hLalt⟩
  have hjunc : ∀ p ∈ (deningerInvList (G := G) L).getLast?,
      ∀ q ∈ ((⟨i, u⟩ : Σ i, G i) :: L).head?, p.1 ≠ q.1 := by
    intro p hp q hq
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
    subst hq
    have hlast := deningerInvList_getLast_fst (G := G) L
    rw [Option.mem_def] at hp
    rw [hp] at hlast
    cases hL : L.head? with
    | none => rw [hL] at hlast; simp at hlast
    | some q' =>
      rw [hL] at hlast
      have : p.1 = q'.1 := by simpa using hlast
      rw [this]
      exact fun hc => hhead q' (by rw [hL]; rfl) hc.symm
  have halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W :=
    List.isChain_append.2 ⟨deningerInvList_isChain L hLalt, hconsalt, hjunc⟩
  have hprod : deningerLetterProd (φ := φ) W =
      (deningerLetterProd (φ := φ) L)⁻¹ * PushoutI.of (φ := φ) i u *
        deningerLetterProd (φ := φ) L := by
    rw [hW, deningerLetterProd_append, deningerLetterProd_cons, ← deningerLetterProd_inv L,
      mul_assoc]
  rw [← hprod, deningerLen_letterProd (d := d) W hred halt, hW]
  simp only [List.length_append, List.length_cons, deningerInvList_length]
  ring

end RHTower
