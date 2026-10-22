import GaloisForLFunctions.RHTower.Deninger.DeningerRotateCycRed
import GaloisForLFunctions.RHTower.Deninger.DeningerBaseConjWord
import GaloisForLFunctions.RHTower.Deninger.DeningerWordIndices

/-!
# A rotation symmetry makes the index sequence periodic

If a cyclically reduced word equals a base conjugate of one of its rotations then both are reduced
alternating words with the same product, so their normal forms agree, and the index sequence is an
invariant of the product.  Hence the index sequence is invariant under the rotation.

* `deningerRotate_sym_map_fst` : the index sequence of a rotation symmetric word is periodic.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **A rotation symmetry makes the index sequence periodic.** -/
theorem deningerRotate_sym_map_fst (U : List (Σ i, G i)) (hne : U ≠ [])
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1) (t : ℕ) (ht : t ≤ U.length) (m : H)
    (hrot : deningerLetterProd (φ := φ) U =
      PushoutI.base φ m * deningerLetterProd (φ := φ) (U.rotate t) * (PushoutI.base φ m)⁻¹) :
    U.map Sigma.fst = (U.rotate t).map Sigma.fst := by
  classical
  obtain ⟨hRred, hRalt, -⟩ := deningerRotate_cycRed (φ := φ) U hred halt hcyc t ht
  have hRne : U.rotate t ≠ [] := by
    intro hc
    exact hne (List.eq_nil_of_length_eq_zero (by
      have := congrArg List.length hc
      simpa using this))
  obtain ⟨W, hWmap, hWred, hWalt, hWprod⟩ :=
    deningerBaseConj_word (U.rotate t) hRne hRred hRalt m
  have hUW : deningerLetterProd (φ := φ) U = deningerLetterProd (φ := φ) W := by
    rw [hrot, hWprod]
  calc U.map Sigma.fst
      = (((deningerLetterProd (φ := φ) U) • (NormalWord.empty : NormalWord d)) :
          NormalWord d).toList.map Sigma.fst := (deningerNormalWord_map_fst (d := d) U hred halt).symm
    _ = (((deningerLetterProd (φ := φ) W) • (NormalWord.empty : NormalWord d)) :
          NormalWord d).toList.map Sigma.fst := by rw [hUW]
    _ = W.map Sigma.fst := deningerNormalWord_map_fst (d := d) W hWred hWalt
    _ = (U.rotate t).map Sigma.fst := hWmap

end RHTower
