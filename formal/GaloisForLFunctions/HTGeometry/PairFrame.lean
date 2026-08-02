import GaloisForLFunctions.HTGeometry.LatticeFrame
import GaloisForLFunctions.HTGeometry.ApartmentZeroClass

/-!
# Two distinct atoms are a frame of their join

The smallest frames have two atoms.  They are the frames the Solomon--Tits descent produces in the
smallest rank, where the link of an apartment is a pair of points, and their apartment class is the
difference of those two points.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe u

section

variable {L : Type u} [CompleteLattice L] {ι : Type u} (e : Fin 2 ≃ ι) {x y T : L}

theorem eq_or_eq_of_equiv_fin_two (j : ι) : j = e 0 ∨ j = e 1 := by
  rcases fin_two_eq (e.symm j) with h | h
  · exact Or.inl (by rw [← Equiv.apply_symm_apply e j, h])
  · exact Or.inr (by rw [← Equiv.apply_symm_apply e j, h])

open scoped Classical in
/-- The two atoms, placed at the two elements of a two-element index. -/
noncomputable def pairAtom (x y : L) (j : ι) : L := if j = e 0 then x else y

omit [CompleteLattice L] in
@[simp] theorem pairAtom_zero (x y : L) : pairAtom e x y (e 0) = x := by
  classical
  exact if_pos rfl

omit [CompleteLattice L] in
@[simp] theorem pairAtom_one (x y : L) (hne : (0 : Fin 2) ≠ 1) :
    pairAtom e x y (e 1) = y := by
  classical
  exact if_neg fun hcon => hne (Equiv.injective e hcon).symm

theorem iSup_pairAtom_ne_zero : (⨆ j, ⨆ (_ : j ≠ e 0), pairAtom e x y j) = y := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  refine le_antisymm (iSup₂_le fun j hj => ?_) ?_
  · rcases eq_or_eq_of_equiv_fin_two e j with h | h
    · exact absurd h hj
    · rw [h, pairAtom_one e x y hne]
  · refine le_of_eq_of_le (pairAtom_one e x y hne).symm ?_
    exact le_iSup₂ (f := fun j (_ : j ≠ e 0) => pairAtom e x y j) (e 1)
      (fun hcon => hne (Equiv.injective e hcon).symm)

theorem iSup_pairAtom_ne_one : (⨆ j, ⨆ (_ : j ≠ e 1), pairAtom e x y j) = x := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  refine le_antisymm (iSup₂_le fun j hj => ?_) ?_
  · rcases eq_or_eq_of_equiv_fin_two e j with h | h
    · rw [h, pairAtom_zero e x y]
    · exact absurd h hj
  · refine le_of_eq_of_le (pairAtom_zero e x y).symm ?_
    exact le_iSup₂ (f := fun j (_ : j ≠ e 1) => pairAtom e x y j) (e 0)
      (fun hcon => hne (Equiv.injective e hcon))

/-- **Two disjoint atoms form a frame of their join.** -/
noncomputable def LatticeFrame.pair (hx : IsAtom x) (hy : IsAtom y) (hxy : Disjoint x y)
    (hsup : x ⊔ y = T) : LatticeFrame L ι T where
  atom := pairAtom e x y
  isAtom j := by
    rcases eq_or_eq_of_equiv_fin_two e j with h | h
    · rw [h, pairAtom_zero e x y]
      exact hx
    · rw [h, pairAtom_one e x y (by decide)]
      exact hy
  indep := by
    refine iSupIndep_def.2 fun j => ?_
    rcases eq_or_eq_of_equiv_fin_two e j with h | h
    · subst h
      rw [pairAtom_zero e x y, iSup_pairAtom_ne_zero]
      exact hxy
    · subst h
      rw [pairAtom_one e x y (by decide), iSup_pairAtom_ne_one]
      exact hxy.symm
  sup_eq := by
    rw [← hsup]
    refine le_antisymm (iSup_le fun j => ?_) (sup_le ?_ ?_)
    · rcases eq_or_eq_of_equiv_fin_two e j with h | h
      · rw [h, pairAtom_zero e x y]
        exact le_sup_left
      · rw [h, pairAtom_one e x y (by decide)]
        exact le_sup_right
    · exact le_of_eq_of_le (pairAtom_zero e x y).symm
        (le_iSup (fun j => pairAtom e x y j) (e 0))
    · exact le_of_eq_of_le (pairAtom_one e x y (by decide)).symm
        (le_iSup (fun j => pairAtom e x y j) (e 1))

@[simp] theorem LatticeFrame.pair_atom (hx : IsAtom x) (hy : IsAtom y) (hxy : Disjoint x y)
    (hsup : x ⊔ y = T) (j : ι) :
    (LatticeFrame.pair e hx hy hxy hsup).atom j = pairAtom e x y j := rfl

end

end GaloisForLFunctions.HTGeometry
