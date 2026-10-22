import GaloisForLFunctions.RHTower.Deninger.DeningerRotate

/-!
# Rotations of a cyclically reduced word

A rotation of a cyclically reduced word is again cyclically reduced: the junction created by the
rotation is an adjacent pair of the original word, and the junction destroyed is the one the cyclic
condition controls.

* `deningerRotate_cycRed` : rotations are cyclically reduced.
* `deningerRotate_one_conj` : conjugating by the first letter rotates by one.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **Rotations of a cyclically reduced word are cyclically reduced.** -/
theorem deningerRotate_cycRed (U : List (Σ i, G i))
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1)
    (t : ℕ) (ht : t ≤ U.length) :
    (∀ p ∈ U.rotate t, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (U.rotate t) ∧
      (∀ p ∈ (U.rotate t).getLast?, ∀ q ∈ (U.rotate t).head?, p.1 ≠ q.1) := by
  refine ⟨fun p hp => hred p (List.mem_rotate.1 hp), ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · rw [List.rotate_zero]
    exact ⟨halt, hcyc⟩
  rcases eq_or_lt_of_le ht with heq | hlt
  · rw [heq, List.rotate_length]
    exact ⟨halt, hcyc⟩
  have hUne : U ≠ [] := fun hc => by rw [hc] at hlt; simp at hlt
  have htakene : U.take t ≠ [] := by
    rw [Ne, List.take_eq_nil_iff]
    push Not
    exact ⟨by omega, hUne⟩
  have hdropne : U.drop t ≠ [] := by
    rw [Ne, List.drop_eq_nil_iff]
    omega
  obtain ⟨htake, hdrop, hjunc⟩ :=
    List.isChain_append.1 (show List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
      (U.take t ++ U.drop t) by rw [List.take_append_drop]; exact halt)
  have hlast : (U.drop t).getLast? = U.getLast? := by
    conv_rhs => rw [← List.take_append_drop t U]
    rw [List.getLast?_append]
    cases hd : (U.drop t).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hd) hdropne
    | some z => simp
  have hhead : (U.take t).head? = U.head? := by
    conv_rhs => rw [← List.take_append_drop t U]
    rw [List.head?_append_of_ne_nil _ htakene]
  rw [List.rotate_eq_drop_append_take ht]
  refine ⟨List.isChain_append.2 ⟨hdrop, htake, fun p hp q hq => ?_⟩, fun p hp q hq => ?_⟩
  · exact hcyc p (hlast ▸ hp) q (hhead ▸ hq)
  · rw [List.getLast?_append] at hp
    rw [List.head?_append_of_ne_nil _ hdropne] at hq
    cases hd : (U.take t).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hd) htakene
    | some z =>
      rw [hd] at hp
      simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact hjunc z hd q hq

/-- **Conjugating by the first letter rotates by one.** -/
theorem deningerRotate_one_conj (U : List (Σ i, G i)) (hne : U ≠ []) :
    ∃ p : Σ i, G i, U.head? = some p ∧
      (PushoutI.of (φ := φ) p.1 p.2)⁻¹ * deningerLetterProd (φ := φ) U *
        PushoutI.of (φ := φ) p.1 p.2 = deningerLetterProd (φ := φ) (U.rotate 1) := by
  cases U with
  | nil => exact absurd rfl hne
  | cons p rest =>
    refine ⟨p, rfl, ?_⟩
    have h1 : (p :: rest).take 1 = [p] := by simp
    have := deningerLetterProd_rotate (φ := φ) (p :: rest) 1 (by simp)
    rw [h1] at this
    have hp : deningerLetterProd (φ := φ) [p] = PushoutI.of (φ := φ) p.1 p.2 := by
      rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
    rw [this, hp]

end RHTower
