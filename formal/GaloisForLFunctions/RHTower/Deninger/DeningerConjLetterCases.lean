import GaloisForLFunctions.RHTower.Deninger.DeningerConjInvariant
import GaloisForLFunctions.RHTower.Deninger.DeningerConjTrichotomy

/-!
# Which cancellation happened

A conjugation by one letter that does not lengthen the word cancels at one of its two ends, and this
records which end and against which letter.  That is what a conjugator has to know about itself in
order to be reconstructed from the rotation.

* `deningerConj_letter_cases` : the cancellation data.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **A conjugation by one letter that does not lengthen cancels at one end**, and this says which
end and against which letter. -/
theorem deningerConj_letter_cases (U : List (Σ i, G i)) (hlen2 : 2 ≤ U.length)
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1)
    (i : ι) (x : G i) (hx : x ∉ (φ i).range)
    (hshort : deningerLen d (PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) U *
      (PushoutI.of (φ := φ) i x)⁻¹) ≤ U.length) :
    (∃ (k : H) (u₁ : G i) (U' : List (Σ i, G i)),
        U = (⟨i, u₁⟩ : Σ i, G i) :: U' ∧ x * u₁ = φ i k) ∨
    (∃ (k : H) (uℓ : G i) (U₀ : List (Σ i, G i)),
        U = U₀ ++ [(⟨i, uℓ⟩ : Σ i, G i)] ∧ uℓ * (x : G i)⁻¹ = φ i k) := by
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
      exact Or.inl ⟨k, q.2, rest, by rw [hU], hk.symm⟩
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
        exact Or.inr ⟨k, p.2, U₀, by rw [hUp], hk.symm⟩
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
