import GaloisForLFunctions.HTGeometry.ApartmentUnnormalizedCycle
import GaloisForLFunctions.HTGeometry.SimplicialPiZeroFree

/-!
# The apartment class of a two-element frame is a difference of two points

A frame with two atoms spans an apartment of dimension zero: two points, one for each ordering of
the frame, entering the fundamental chain with opposite signs.  So its class in degree-zero homology
is the difference of the classes of those two points, and under the identification of degree-zero
homology with the coproduct over the components it is the difference of the two basis elements.

This is the shape the Solomon--Tits descent takes in the smallest rank, where the link of an
apartment is a pair of points rather than a sphere.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

section Perm

theorem fin_two_eq (x : Fin 2) : x = 0 ∨ x = 1 :=
  (Fin.forall_fin_two (p := fun i => i = 0 ∨ i = 1)).2 ⟨Or.inl rfl, Or.inr rfl⟩ x

/-- A permutation of two places is the identity or the transposition. -/
theorem perm_fin_two (σ : Equiv.Perm (Fin 2)) : σ = 1 ∨ σ = Equiv.swap 0 1 := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  by_cases h : σ 0 = 0
  · refine Or.inl (Equiv.ext fun x => ?_)
    have h1 : σ 1 = 1 := by
      by_contra hcon
      have : σ 1 = 0 := by
        rcases (fin_two_eq (σ 1)) with h0 | h0
        · exact h0
        · exact absurd h0 hcon
      exact hne ((σ.injective (this.trans h.symm)).symm)
    rcases fin_two_eq x with rfl | rfl
    · exact h
    · exact h1
  · have h0 : σ 0 = 1 := by
      rcases fin_two_eq (σ 0) with h' | h'
      · exact absurd h' h
      · exact h'
    have h1 : σ 1 = 0 := by
      rcases fin_two_eq (σ 1) with h' | h'
      · exact h'
      · exact absurd (σ.injective (h'.trans h0.symm)) (Ne.symm hne)
    refine Or.inr (Equiv.ext fun x => ?_)
    rcases fin_two_eq x with rfl | rfl
    · rw [h0, Equiv.swap_apply_left]
    · rw [h1, Equiv.swap_apply_right]

theorem univ_perm_fin_two :
    (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
  classical
  refine Finset.eq_of_subset_of_card_le (fun σ _ => ?_) ?_
  · rcases perm_fin_two σ with h | h
    · exact h ▸ Finset.mem_insert_self _ _
    · exact h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
      intro hcon
      have := congrArg (fun t : Equiv.Perm (Fin 2) => t 0) hcon
      rw [Equiv.swap_apply_left] at this
      exact absurd this (by decide)
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton,
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]

end Perm

section Zero

variable {ι : Type u} {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{u} C]

/-- **The fundamental chain of a two-element frame is the difference of its two points.** -/
theorem apartmentChainIn_zero (e₀ : Fin (0 + 2) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) :
    apartmentChainIn e₀ g R Finset.univ
      = X.ιChainComplex (R := R) (g.app (op ⦋0⦌) (apartmentChainSimplex e₀))
        - X.ιChainComplex (R := R)
          (g.app (op ⦋0⦌) (apartmentChainSimplex ((Equiv.swap 0 1).trans e₀))) := by
  classical
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro hcon
    have := congrArg (fun t : Equiv.Perm (Fin 2) => t 0) hcon
    rw [Equiv.swap_apply_left] at this
    exact absurd this (by decide)
  rw [apartmentChainIn, univ_perm_fin_two, Finset.sum_pair hne,
    show ((1 : Equiv.Perm (Fin 2)).trans e₀) = e₀ from Equiv.refl_trans e₀,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp [sub_eq_add_neg]

end Zero

section ZeroClass

variable {ι : Type u} {C : Type u} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]

/-- **The apartment class of a two-element frame is the difference of the classes of its two
points.** -/
theorem apartmentClassIn_zero (e₀ : Fin (0 + 2) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) :
    apartmentClassIn e₀ g R
      = zeroCycle X R (g.app (op ⦋0⦌) (apartmentChainSimplex e₀))
        - zeroCycle X R (g.app (op ⦋0⦌)
          (apartmentChainSimplex ((Equiv.swap 0 1).trans e₀))) := by
  have hcyc : apartmentCycleIn e₀ g R
      = (X.chainComplex R).liftCycles
          (X.ιChainComplex (R := R) (g.app (op ⦋0⦌) (apartmentChainSimplex e₀))) 0 (by simp)
          (by simp)
        - (X.chainComplex R).liftCycles
          (X.ιChainComplex (R := R) (g.app (op ⦋0⦌)
            (apartmentChainSimplex ((Equiv.swap 0 1).trans e₀)))) 0 (by simp) (by simp) := by
    rw [← cancel_mono ((X.chainComplex R).iCycles 0), apartmentCycleIn_i,
      Preadditive.sub_comp, HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i,
      apartmentChainIn_zero]
  rw [apartmentClassIn, hcyc, Preadditive.sub_comp, zeroCycle, zeroCycle]

/-- **And in the coproduct over the components it is the difference of two basis elements.** -/
theorem apartmentClassIn_zero_comp_homology₀Iso (e₀ : Fin (0 + 2) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) :
    apartmentClassIn e₀ g R ≫ (X.homology₀Iso R).hom
      = Limits.Sigma.ι (fun _ : SSet.π₀ X => R)
          (SSet.π₀.mk (g.app (op ⦋0⦌) (apartmentChainSimplex e₀)))
        - Limits.Sigma.ι (fun _ : SSet.π₀ X => R)
          (SSet.π₀.mk (g.app (op ⦋0⦌)
            (apartmentChainSimplex ((Equiv.swap 0 1).trans e₀)))) := by
  rw [apartmentClassIn_zero, Preadditive.sub_comp, zeroCycle_comp_homology₀Iso,
    zeroCycle_comp_homology₀Iso]

end ZeroClass

end GaloisForLFunctions.HTGeometry
