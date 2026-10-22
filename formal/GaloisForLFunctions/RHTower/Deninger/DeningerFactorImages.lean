import GaloisForLFunctions.RHTower.Deninger.DeningerFactorEltIsolated

/-!
# The images of two different factors meet in the base group

An element of one factor which equals an element of another is in the base group: otherwise the two
one letter words would be reduced and would have to run through the same factor.  So the images of
two different factors intersect exactly in the image of the base group.

* `deningerOf_eq_cross` : the intersection.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **An element of one factor equal to an element of another lies in the base group.** -/
theorem deningerOf_eq_cross (hφ : ∀ i, Function.Injective (φ i)) (i j : ι) (hij : i ≠ j)
    (x : G i) (y : G j) (h : PushoutI.of (φ := φ) i x = PushoutI.of (φ := φ) j y) :
    x ∈ (φ i).range := by
  classical
  by_contra hx
  by_cases hy : y ∈ (φ j).range
  · obtain ⟨k, hk⟩ := hy
    refine hx ⟨k, ?_⟩
    refine PushoutI.of_injective hφ i ?_
    rw [PushoutI.of_apply_eq_base φ i k, h, ← hk, PushoutI.of_apply_eq_base φ j k]
  · have hprod : deningerLetterProd (φ := φ) [(⟨i, x⟩ : Σ i, G i)] =
        deningerLetterProd (φ := φ) [(⟨j, y⟩ : Σ i, G i)] := by
      rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one, deningerLetterProd_cons,
        deningerLetterProd_nil, mul_one]
      exact h
    have hfst := deningerWords_map_fst_eq (d := d) [(⟨i, x⟩ : Σ i, G i)] [(⟨j, y⟩ : Σ i, G i)]
      (by simpa using hx) (List.isChain_singleton _) (by simpa using hy)
      (List.isChain_singleton _) hprod
    exact hij (by simpa using hfst)

end RHTower
