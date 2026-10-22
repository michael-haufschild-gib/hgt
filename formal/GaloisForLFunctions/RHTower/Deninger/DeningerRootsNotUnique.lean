import GaloisForLFunctions.RHTower.Deninger.DeningerRootBase

/-!
# Roots in an amalgam need not be unique

If two factors contain elements outside the base group whose `n`-th powers are the same element of
the base group, then those elements have the same `n`-th power in the amalgam but are distinct.  So
an amalgam of groups with unique roots need not have unique roots: the amalgamated subgroup has to
be isolated in the factors for that.

* `deningerPow_eq_ne` : the criterion for non uniqueness.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Roots in an amalgam need not be unique.**  Two elements of different factors, neither in the
base group, whose `n`-th powers are the same element of the base group, are distinct with the same
`n`-th power. -/
theorem deningerPow_eq_ne (i j : ι) (hij : i ≠ j) (a : G i) (b : G j) (s : H) (n : ℕ)
    (ha : a ∉ (φ i).range) (hb : b ∉ (φ j).range)
    (han : a ^ n = φ i s) (hbn : b ^ n = φ j s) :
    (PushoutI.of (φ := φ) i a) ^ n = (PushoutI.of (φ := φ) j b) ^ n ∧
      PushoutI.of (φ := φ) i a ≠ PushoutI.of (φ := φ) j b := by
  constructor
  · rw [← map_pow, ← map_pow, han, hbn, PushoutI.of_apply_eq_base, PushoutI.of_apply_eq_base]
  · intro hc
    refine hij ?_
    have hprod : deningerLetterProd (φ := φ) [(⟨i, a⟩ : Σ i, G i)] =
        deningerLetterProd (φ := φ) [(⟨j, b⟩ : Σ i, G i)] := by
      rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one, deningerLetterProd_cons,
        deningerLetterProd_nil, mul_one]
      exact hc
    have := deningerWords_map_fst_eq (d := d) [(⟨i, a⟩ : Σ i, G i)] [(⟨j, b⟩ : Σ i, G i)]
      (by simpa using ha) (List.isChain_singleton _) (by simpa using hb)
      (List.isChain_singleton _) hprod
    simpa using this

end RHTower
