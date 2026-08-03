import GaloisForLFunctions.RHTower.DeningerConjCycRed

/-!
# Elements with a short power

A cyclically reduced word satisfying the cyclic condition has at least two letters, so the length of
a power of an element whose cyclic word is of that kind grows with the exponent.  An element whose
square or higher power has length at most one therefore has a cyclic word of one letter: it is a
base group element or a conjugate of a factor element.

* `deningerCycRed_two_le` : a cyclically reduced word has at least two letters.
* `deningerConj_factor_of_pow_len_le_one` : the classification of elements with a short power.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **A cyclically reduced word has at least two letters**: a single letter is its own first and
last, so the cyclic condition would make its index differ from itself. -/
theorem deningerCycRed_two_le (V : List (Σ i, G i)) (hVne : V ≠ [])
    (hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) : 2 ≤ V.length := by
  by_contra hlt
  obtain ⟨p, hp⟩ : ∃ p, V = [p] := by
    refine List.length_eq_one_iff.1 ?_
    have := List.length_pos_iff.2 hVne
    omega
  subst hp
  exact hVcyc p (by simp) p (by simp) rfl

include d in
/-- **The classification of elements with a short power.**  An element whose square or higher power
has length at most one is a base group element or a conjugate of a factor element. -/
theorem deningerConj_factor_of_pow_len_le_one (x : PushoutI φ) (n : ℕ)
    (hlen : deningerLen d (x ^ (n + 2)) ≤ 1) :
    (∃ h : H, x = PushoutI.base φ h) ∨
      ∃ (c : PushoutI φ) (i : ι) (a : G i), x = c⁻¹ * PushoutI.of (φ := φ) i a * c := by
  classical
  rcases deningerExists_letterProd (d := d) x with ⟨h₀, hxb, -⟩ | ⟨L, hLne, hLred, hLalt, -, hxL⟩
  · exact Or.inl ⟨h₀, hxb⟩
  obtain ⟨C, R, V, hsplit, -, hVne, hVred, hValt, hhead, hprod, hdisj, -⟩ :=
    deningerExists_cycData_len (φ := φ) L hLne hLred hLalt
  subst hsplit
  have hconj : deningerLetterProd (φ := φ) (C ++ R) =
      deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) V *
        (deningerLetterProd (φ := φ) C)⁻¹ := (deningerCycData_iff C R V).2 hprod
  rcases hdisj with hshort | hVcyc
  · obtain ⟨p, hp⟩ : ∃ p, V = [p] := by
      refine List.length_eq_one_iff.1 ?_
      have := List.length_pos_iff.2 hVne
      omega
    refine Or.inr ⟨(deningerLetterProd (φ := φ) C)⁻¹, p.1, p.2, ?_⟩
    rw [inv_inv, hxL, hconj, hp, deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
  · exfalso
    have hlenpow : deningerLen d ((deningerLetterProd (φ := φ) (C ++ R)) ^ (n + 2)) =
        C.length + (n + 1) * V.length + R.length :=
      deningerLen_conj_pow (d := d) C R V hLred hLalt hVne hVred hValt hVcyc hhead hprod (n + 1)
    have h2 : 2 ≤ V.length := deningerCycRed_two_le V hVne hVcyc
    rw [← hxL] at hlenpow
    have : 2 ≤ (n + 1) * V.length := by
      calc 2 = 1 * 2 := by ring
        _ ≤ (n + 1) * V.length := Nat.mul_le_mul (by omega) h2
    omega

end RHTower
