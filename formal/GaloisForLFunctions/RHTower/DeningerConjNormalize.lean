import GaloisForLFunctions.RHTower.DeningerConjWord

/-!
# Normalizing a conjugator

A conjugator is only determined up to multiplication by the base group on the right, and that
freedom can be used to make its inverse a transversal word.  This is what puts a conjugated power
into the shape whose normal word is a plain concatenation.

* `deningerExists_inv_transversal` : the normalized conjugator.
* `deningerConj_transversal_form` : a conjugate written with a transversal conjugator.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **The normalized conjugator.**  Every element can be multiplied by an element of the base group
on the right so that its inverse becomes a transversal word. -/
theorem deningerExists_inv_transversal (c : PushoutI φ) :
    ∃ (h : H) (D : List (Σ i, G i)),
      (∀ p ∈ D, p.2 ∈ d.set p.1) ∧ (∀ p ∈ D, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) D ∧
      (c * PushoutI.base φ h)⁻¹ = deningerLetterProd (φ := φ) D := by
  rcases deningerExists_letterProd (d := d) c⁻¹ with ⟨h₀, hc, _⟩ | ⟨L, _, hred, halt, _, hc⟩
  · refine ⟨h₀, [], by simp, by simp, by simp, ?_⟩
    rw [mul_inv_rev, ← map_inv, hc, deningerLetterProd_nil, ← map_mul, inv_mul_cancel, map_one]
  · obtain ⟨h₁, D, hmap, hset, hredD, heq⟩ :=
      deningerExists_transversal_form (d := d) L hred
    refine ⟨h₁, D, hset, hredD, deningerIsChain_of_map_fst L D hmap halt, ?_⟩
    rw [mul_inv_rev, ← map_inv, hc, heq, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- **A conjugate written with a transversal conjugator.**  The base group element absorbed into the
conjugator reappears as a conjugation of the conjugated element by the base group, which does not
change its word length. -/
theorem deningerConj_transversal_form (g c u : PushoutI φ) (hg : g = c * u * c⁻¹) :
    ∃ (h : H) (D : List (Σ i, G i)),
      (∀ p ∈ D, p.2 ∈ d.set p.1) ∧ (∀ p ∈ D, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) D ∧
      g = (deningerLetterProd (φ := φ) D)⁻¹ *
        (PushoutI.base φ h⁻¹ * u * PushoutI.base φ h) * deningerLetterProd (φ := φ) D := by
  obtain ⟨h, D, hset, hred, halt, hD⟩ := deningerExists_inv_transversal (d := d) c
  refine ⟨h, D, hset, hred, halt, ?_⟩
  have hc : c * PushoutI.base φ h = (deningerLetterProd (φ := φ) D)⁻¹ := by
    rw [← hD, inv_inv]
  have hDD : deningerLetterProd (φ := φ) D = PushoutI.base φ h⁻¹ * c⁻¹ := by
    rw [← hD, mul_inv_rev, ← map_inv]
  rw [hg, ← hc, hDD, map_inv]
  group

end RHTower
