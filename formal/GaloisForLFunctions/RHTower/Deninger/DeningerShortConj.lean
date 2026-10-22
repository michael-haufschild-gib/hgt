import GaloisForLFunctions.RHTower.Deninger.DeningerFactorConjOfPow

/-!
# Conjugating a factor element by a letter

Conjugating an element of a factor by a letter of the same factor stays in that factor.  Conjugating
it by a letter of another factor does not: the three letters alternate and none is in the base
group, so the conjugate is a reduced word of three letters.  This is the case distinction on which
the conjugacy of short elements turns.

* `deningerConj_letter_same` : conjugation inside a factor.
* `deningerLen_conj_letter_cross` : conjugation across factors lengthens to three.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **Conjugation inside a factor stays in the factor.** -/
theorem deningerConj_letter_same (i : ι) (u x : G i) :
    (PushoutI.of (φ := φ) i x)⁻¹ * PushoutI.of (φ := φ) i u * PushoutI.of (φ := φ) i x =
      PushoutI.of (φ := φ) i (x⁻¹ * u * x) := by
  rw [map_mul, map_mul, map_inv]

include d in
/-- **Conjugation across factors lengthens to three.** -/
theorem deningerLen_conj_letter_cross (i j : ι) (hij : j ≠ i) (u : G i) (y : G j)
    (hu : u ∉ (φ i).range) (hy : y ∉ (φ j).range) :
    deningerLen d ((PushoutI.of (φ := φ) j y)⁻¹ * PushoutI.of (φ := φ) i u *
      PushoutI.of (φ := φ) j y) = 3 := by
  have hyinv : y⁻¹ ∉ (φ j).range := by
    intro hmem
    obtain ⟨w, hw⟩ := hmem
    exact hy ⟨w⁻¹, by rw [map_inv, hw, inv_inv]⟩
  set L : List (Σ i, G i) :=
    [(⟨j, y⁻¹⟩ : Σ i, G i), (⟨i, u⟩ : Σ i, G i), (⟨j, y⟩ : Σ i, G i)] with hL
  have hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range := by
    intro p hp
    rw [hL] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hyinv
    · exact hu
    · exact hy
  have halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L := by
    rw [hL]
    refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_, List.isChain_singleton _⟩⟩
    · intro q hq
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      exact hij
    · intro q hq
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      exact fun hc => hij hc.symm
  have hprod : deningerLetterProd (φ := φ) L =
      (PushoutI.of (φ := φ) j y)⁻¹ * PushoutI.of (φ := φ) i u * PushoutI.of (φ := φ) j y := by
    rw [hL, deningerLetterProd_cons, deningerLetterProd_cons, deningerLetterProd_cons,
      deningerLetterProd_nil, mul_one, map_inv, mul_assoc]
  rw [← hprod, deningerLen_letterProd (d := d) L hred halt, hL]
  simp

end RHTower
