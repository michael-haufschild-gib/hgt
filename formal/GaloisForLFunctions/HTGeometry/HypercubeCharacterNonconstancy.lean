import GaloisForLFunctions.HTGeometry.BooleanHypercubeTranspositionLaw

/-!
# A nonconstant hypercube character is nonconstant across some edge

Patching coordinates one at a time turns any two Boolean vertices into a chain of hypercube edges,
so a function which is unchanged by every single-coordinate toggle is constant.  Contrapositively, a
character taking two different values differs across some edge.

This selects the qubit whose transverse coupling escapes a given spectral character: the block
differences of that coupling are exactly the edge differences of the character.
-/

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ} {M : Type*}

theorem boolPatch_empty (x y : Fin n → Bool) : boolPatch x y ∅ = x := by
  funext j
  simp [boolPatch]

theorem boolPatch_univ (x y : Fin n → Bool) : boolPatch x y Finset.univ = y := by
  funext j
  simp [boolPatch]

/-- Adding one coordinate to the patch either changes nothing or toggles exactly that
coordinate. -/
theorem boolPatch_insert (x y : Fin n → Bool) (s : Finset (Fin n)) {i : Fin n} (hi : i ∉ s) :
    boolPatch x y (insert i s) = boolPatch x y s ∨
      boolPatch x y (insert i s) = boolToggle (boolPatch x y s) i := by
  classical
  by_cases hxy : y i = x i
  · left
    funext j
    by_cases hji : j = i
    · subst hji
      simp [boolPatch, hi, hxy]
    · simp [boolPatch, hji, Finset.mem_insert]
  · right
    funext j
    by_cases hji : j = i
    · subst hji
      have hxi : boolPatch x y s j = x j := by simp only [boolPatch, if_neg hi]
      have hyx : y j = !x j := by
        rcases Bool.eq_false_or_eq_true (x j) with hx | hx <;>
          rcases Bool.eq_false_or_eq_true (y j) with hy | hy <;>
            simp [hx, hy] at hxy ⊢
      rw [show boolPatch x y (insert j s) j = y j by simp [boolPatch],
        show boolToggle (boolPatch x y s) j j = !(boolPatch x y s j) by simp [boolToggle],
        hxi, hyx]
    · simp [boolPatch, boolToggle, hji, Finset.mem_insert]

/-- **A character unchanged by every edge toggle is constant.** -/
theorem const_of_boolToggle_const (k : (Fin n → Bool) → M)
    (hedge : ∀ (z : Fin n → Bool) (i : Fin n), k (boolToggle z i) = k z) (x y : Fin n → Bool) :
    k x = k y := by
  classical
  have hpatch : ∀ s : Finset (Fin n), k (boolPatch x y s) = k x := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [boolPatch_empty]
    | @insert i s hi ih =>
        rcases boolPatch_insert x y s hi with hcase | hcase
        · rw [hcase, ih]
        · rw [hcase, hedge, ih]
  have huniv := hpatch Finset.univ
  rw [boolPatch_univ] at huniv
  exact huniv.symm

/-- **A nonconstant character differs across some hypercube edge.**  This is the qubit selection
behind the block-splitting escape. -/
theorem exists_boolToggle_ne_of_ne (k : (Fin n → Bool) → M) {x y : Fin n → Bool}
    (hxy : k x ≠ k y) :
    ∃ (z : Fin n → Bool) (i : Fin n), k (boolToggle z i) ≠ k z := by
  by_contra hcon
  push Not at hcon
  exact hxy (const_of_boolToggle_const k (fun z i => hcon z i) x y)

end GaloisForLFunctions.HTGeometry
