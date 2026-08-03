import GaloisForLFunctions.RHTower.DeningerConjLast

/-!
# The one letter trichotomy

Conjugating a cyclically reduced word of at least two letters by a single letter either lengthens
it, or is a rotation up to the base group.  Lengthening happens unless the letter comes from one of
the two extreme factors and cancels the extreme letter into the base group, and cancellation is
exactly rotation.

* `deningerConj_letter_rotate` : a conjugation that does not lengthen is a rotation.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **A conjugation by one letter that does not lengthen is a rotation.** -/
theorem deningerConj_letter_rotate (U : List (Σ i, G i)) (hlen2 : 2 ≤ U.length)
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1)
    (i : ι) (x : G i) (hx : x ∉ (φ i).range)
    (hshort : deningerLen d (PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) U *
      (PushoutI.of (φ := φ) i x)⁻¹) ≤ U.length) :
    ∃ (t : ℕ) (m : H), t ≤ U.length ∧
      PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) U *
          (PushoutI.of (φ := φ) i x)⁻¹ =
        PushoutI.base φ m * deningerLetterProd (φ := φ) (U.rotate t) *
          (PushoutI.base φ m)⁻¹ := by
  classical
  obtain ⟨q, rest, hU⟩ : ∃ q rest, U = q :: rest := by
    cases U with
    | nil => simp at hlen2
    | cons q rest => exact ⟨q, rest, rfl⟩
  have hrestne : rest ≠ [] := by
    intro hc
    rw [hU, hc] at hlen2
    simp at hlen2
  have hUhead : U.head? = some q := by rw [hU, List.head?_cons]
  obtain ⟨U₀, p, hUp⟩ : ∃ U₀ p, U = U₀ ++ [p] := by
    obtain ⟨w, hw⟩ : ∃ w, U.getLast? = some w := by
      cases hUg : U.getLast? with
      | none =>
        rw [List.getLast?_eq_none_iff.1 hUg] at hlen2
        simp at hlen2
      | some w => exact ⟨w, rfl⟩
    exact ⟨U.dropLast, w, (List.dropLast_append_getLast? _ hw).symm⟩
  have hUlast : U.getLast? = some p := by rw [hUp]; simp
  have hU₀ne : U₀ ≠ [] := by
    intro hc
    rw [hUp, hc] at hlen2
    simp at hlen2
  by_cases hiq : q.1 = i
  · subst hiq
    have hqeta : (⟨q.1, q.2⟩ : Σ i, G i) = q := rfl
    by_cases hmem : x * q.2 ∈ (φ q.1).range
    · obtain ⟨k, hk⟩ := hmem
      refine ⟨1, k, by omega, ?_⟩
      have := deningerConj_head_merge (φ := φ) q.1 q.2 rest x k hk.symm
      rw [hqeta] at this
      rw [hU]
      exact this
    · exfalso
      have hlast' : ∀ r ∈ rest.getLast?, r.1 ≠ q.1 := by
        intro r hr
        refine hcyc r ?_ q hUhead
        rw [hU, List.getLast?_cons_of_ne_nil hrestne]
        exact hr
      have hcalc := deningerLen_conj_head_ne (d := d) q.1 q.2 rest hrestne
        (by rw [hqeta, ← hU]; exact hred) (by rw [hqeta, ← hU]; exact halt) hlast' x hx hmem
      rw [hqeta, ← hU] at hcalc
      have hUlen : U.length = rest.length + 1 := by rw [hU]; simp
      omega
  · by_cases hip : p.1 = i
    · subst hip
      have hpeta : (⟨p.1, p.2⟩ : Σ i, G i) = p := rfl
      have hhead' : ∀ r ∈ U₀.head?, p.1 ≠ r.1 := by
        intro r hr
        refine hcyc p hUlast r ?_
        rw [hUp, List.head?_append_of_ne_nil _ hU₀ne]
        exact hr
      by_cases hmem : p.2 * (x : G p.1)⁻¹ ∈ (φ p.1).range
      · obtain ⟨k, hk⟩ := hmem
        refine ⟨U₀.length, k⁻¹, by rw [hUp]; simp, ?_⟩
        have := deningerConj_last_merge (φ := φ) p.1 p.2 U₀ x k hk.symm
        rw [hpeta] at this
        rw [hUp]
        exact this
      · exfalso
        have hcalc := deningerLen_conj_last_ne (d := d) p.1 p.2 U₀ hU₀ne
          (by rw [hpeta, ← hUp]; exact hred) (by rw [hpeta, ← hUp]; exact halt) hhead' x hx hmem
        rw [hpeta, ← hUp] at hcalc
        have hUlen : U.length = U₀.length + 1 := by rw [hUp]; simp
        omega
    · exfalso
      have hne : U ≠ [] := by rw [hU]; simp
      have hhead' : ∀ r ∈ U.head?, i ≠ r.1 := by
        intro r hr
        rw [hUhead, Option.mem_def, Option.some.injEq] at hr
        subst hr
        exact fun hc => hiq hc.symm
      have hlast' : ∀ r ∈ U.getLast?, r.1 ≠ i := by
        intro r hr
        rw [hUlast, Option.mem_def, Option.some.injEq] at hr
        subst hr
        exact hip
      have hcalc := deningerLen_conj_letter_ne (d := d) U hne hred halt i x hx hhead' hlast'
      omega

end RHTower
