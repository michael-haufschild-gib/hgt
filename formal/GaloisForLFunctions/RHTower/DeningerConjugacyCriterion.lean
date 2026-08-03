import GaloisForLFunctions.RHTower.DeningerConjWordForm

/-!
# The conjugacy criterion

An element conjugating a cyclically reduced word of at least two letters to something no longer than
itself does so by a rotation, up to the base group.  The conjugating word is peeled one letter at a
time: each letter either rotates, or lengthens the word irreversibly, since the lengthened word
carries that letter at both ends and the rest of the conjugating word alternates away from it.

* `deningerConj_cycRed_rotate` : the criterion.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The conjugacy criterion.**  A conjugate of a cyclically reduced word of at least two letters
which is no longer than the word is a rotation of it, up to the base group. -/
theorem deningerConj_cycRed_rotate (A U : List (Σ i, G i))
    (hAred : ∀ p ∈ A, p.2 ∉ (φ p.1).range)
    (hAalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) A)
    (hlen2 : 2 ≤ U.length)
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1)
    (hshort : deningerLen d (deningerLetterProd (φ := φ) A * deningerLetterProd (φ := φ) U *
      (deningerLetterProd (φ := φ) A)⁻¹) ≤ U.length) :
    ∃ (t : ℕ) (m : H), t ≤ U.length ∧
      deningerLetterProd (φ := φ) A * deningerLetterProd (φ := φ) U *
          (deningerLetterProd (φ := φ) A)⁻¹ =
        PushoutI.base φ m * deningerLetterProd (φ := φ) (U.rotate t) *
          (PushoutI.base φ m)⁻¹ := by
  classical
  suffices Hn : ∀ n : ℕ, ∀ A U : List (Σ i, G i), A.length ≤ n →
      (∀ p ∈ A, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) A →
      2 ≤ U.length →
      (∀ p ∈ U, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U →
      (∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1) →
      deningerLen d (deningerLetterProd (φ := φ) A * deningerLetterProd (φ := φ) U *
        (deningerLetterProd (φ := φ) A)⁻¹) ≤ U.length →
      ∃ (t : ℕ) (m : H), t ≤ U.length ∧
        deningerLetterProd (φ := φ) A * deningerLetterProd (φ := φ) U *
            (deningerLetterProd (φ := φ) A)⁻¹ =
          PushoutI.base φ m * deningerLetterProd (φ := φ) (U.rotate t) *
            (PushoutI.base φ m)⁻¹ from
    Hn A.length A U le_rfl hAred hAalt hlen2 hred halt hcyc hshort
  clear hshort hcyc halt hred hlen2 hAalt hAred A U
  intro n
  induction n with
  | zero =>
    intro A U hn _ _ hlen2 _ _ _ _
    have hA : A = [] := List.length_eq_zero_iff.1 (by omega)
    subst hA
    exact ⟨0, 1, by omega, by simp⟩
  | succ n ih =>
    intro A U hn hAred hAalt hlen2 hred halt hcyc hshort
    rcases eq_or_ne A [] with rfl | hAne
    · exact ⟨0, 1, by omega, by simp⟩
    obtain ⟨A', a, hA⟩ : ∃ A' a, A = A' ++ [a] := by
      obtain ⟨w, hw⟩ : ∃ w, A.getLast? = some w := by
        cases hAg : A.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.1 hAg) hAne
        | some w => exact ⟨w, rfl⟩
      exact ⟨A.dropLast, w, (List.dropLast_append_getLast? _ hw).symm⟩
    obtain ⟨hA'alt, _, hjunc⟩ := List.isChain_append.1 (by rw [← hA]; exact hAalt)
    have hA'red : ∀ p ∈ A', p.2 ∉ (φ p.1).range := fun p hp =>
      hAred p (by rw [hA]; exact List.mem_append.2 (Or.inl hp))
    have hared : a.2 ∉ (φ a.1).range := hAred a (by rw [hA]; simp)
    have hA'last : ∀ p ∈ A'.getLast?, p.1 ≠ a.1 := fun p hp => hjunc p hp a rfl
    have hsplit : deningerLetterProd (φ := φ) A * deningerLetterProd (φ := φ) U *
        (deningerLetterProd (φ := φ) A)⁻¹ =
        deningerLetterProd (φ := φ) A' *
          (PushoutI.of (φ := φ) a.1 a.2 * deningerLetterProd (φ := φ) U *
            (PushoutI.of (φ := φ) a.1 a.2)⁻¹) * (deningerLetterProd (φ := φ) A')⁻¹ := by
      rw [hA, deningerLetterProd_snoc, mul_inv_rev]
      group
    rcases deningerConj_letter_word (φ := φ) U hlen2 hred halt hcyc a.1 a.2 hared with
      ⟨t₀, m₀, ht₀, hrot⟩ | ⟨W, hWeq, hWred, hWalt, hWlen, hWhead, hWlast⟩
    · have hrotcyc := deningerRotate_cycRed (φ := φ) U hred halt hcyc t₀ ht₀
      have hrotlen : (U.rotate t₀).length = U.length := List.length_rotate _ _
      rcases eq_or_ne A' [] with hA'nil | hA'ne
      · refine ⟨t₀, m₀, ht₀, ?_⟩
        rw [hsplit, hrot, hA'nil]
        simp
      · obtain ⟨A'', b, hA'⟩ : ∃ A'' b, A' = A'' ++ [b] := by
          obtain ⟨w, hw⟩ : ∃ w, A'.getLast? = some w := by
            cases hA'g : A'.getLast? with
            | none => exact absurd (List.getLast?_eq_none_iff.1 hA'g) hA'ne
            | some w => exact ⟨w, rfl⟩
          exact ⟨A'.dropLast, w, (List.dropLast_append_getLast? _ hw).symm⟩
        set B : List (Σ i, G i) := A'' ++ [(⟨b.1, b.2 * φ b.1 m₀⟩ : Σ i, G i)] with hB
        have hBprod : deningerLetterProd (φ := φ) B =
            deningerLetterProd (φ := φ) A' * PushoutI.base φ m₀ := by
          rw [hB, ← deningerLetterProd_mul_base_snoc, hA']
        have hBred : ∀ p ∈ B, p.2 ∉ (φ p.1).range :=
          deningerAbsorbRight_reduced A'' b m₀ (by rw [← hA']; exact hA'red)
        have hBfst : B.map Sigma.fst = A'.map Sigma.fst := by
          rw [hB, deningerAbsorbRight_map_fst A'' b m₀, hA']
        have hBalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) B :=
          deningerIsChain_of_map_fst A' B hBfst hA'alt
        have hBlen : B.length ≤ n := by
          have h1 : B.length = A'.length := by
            have := congrArg List.length hBfst
            simpa using this
          have h2 : A.length = A'.length + 1 := by rw [hA]; simp
          omega
        have hconj : deningerLetterProd (φ := φ) A * deningerLetterProd (φ := φ) U *
            (deningerLetterProd (φ := φ) A)⁻¹ =
            deningerLetterProd (φ := φ) B * deningerLetterProd (φ := φ) (U.rotate t₀) *
              (deningerLetterProd (φ := φ) B)⁻¹ := by
          rw [hsplit, hrot, hBprod, mul_inv_rev]
          group
        obtain ⟨t₁, m₁, ht₁, heq⟩ := ih B (U.rotate t₀) hBlen hBred hBalt (by omega)
          hrotcyc.1 hrotcyc.2.1 hrotcyc.2.2 (by rw [← hconj, hrotlen]; exact hshort)
        refine ⟨(t₀ + t₁) % U.length, m₁, le_of_lt (Nat.mod_lt _ (by omega)), ?_⟩
        rw [hconj, heq, List.rotate_rotate, List.rotate_mod]
    · exfalso
      have hWne : W ≠ [] := by
        intro hc
        rw [hc] at hWlen
        simp at hWlen
      have hAV : ∀ p ∈ A'.getLast?, ∀ q ∈ W.head?, p.1 ≠ q.1 := by
        intro p hp q hq
        rw [hWhead q hq]
        exact hA'last p hp
      have hVA : ∀ p ∈ W.getLast?, ∀ q ∈ A'.getLast?, p.1 ≠ q.1 := by
        intro p hp q hq
        rw [hWlast p hp]
        exact fun hc => hA'last q hq hc.symm
      have hcalc := deningerLen_conj_word (d := d) A' W hA'red hA'alt hWred hWalt hWne hAV hVA
      rw [hsplit, hWeq] at hshort
      omega

end RHTower
