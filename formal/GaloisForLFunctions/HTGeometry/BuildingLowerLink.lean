import GaloisForLFunctions.HTGeometry.BuildingLinkHomology
import GaloisForLFunctions.HTGeometry.NerveVertexRemoval

/-!
# The lower link of a subspace is the building of that subspace

Dual to the identification of the upper link with the building of the quotient: the proper nonzero
subspaces strictly below `p` are the proper nonzero subspaces of `p` itself.

Together with the punctured star being the union of the two links, this completes the local picture
at a vertex of a building: removing a vertex leaves the two smaller buildings that sit below and
above it.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u

variable {P : Type u} [PartialOrder P]

/-- **The punctured star is the union of the two links.** -/
theorem generalStar_inter_compl_eq (p : P) :
    generalStar p ∩ {q : P | q ≠ p} = {q : P | q < p} ∪ {q : P | p < q} := by
  ext q
  constructor
  · rintro ⟨hcomp, hne⟩
    rcases hcomp with h | h
    · exact Or.inl (lt_of_le_of_ne h hne)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hne))
  · rintro (h | h)
    · exact ⟨Or.inl (le_of_lt h), ne_of_lt h⟩
    · exact ⟨Or.inr (le_of_lt h), Ne.symm (ne_of_lt h)⟩

/-- **At a maximal element the punctured star is the lower link alone.** -/
theorem generalStar_inter_compl_eq_of_maximal (p : P) (hmax : ∀ q, p ≤ q → q = p) :
    generalStar p ∩ {q : P | q ≠ p} = {q : P | q < p} := by
  rw [generalStar_inter_compl_eq]
  refine Set.union_eq_self_of_subset_right (fun q hq => ?_)
  exact absurd (hmax q (le_of_lt hq)) (Ne.symm (ne_of_lt hq))

variable {R : Type*} {M : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- **The lower link of a subspace is the building of that subspace.** -/
def lowerLinkOrderIso (p : Submodule R M) :
    {W : Submodule R (p : Type u) // ⊥ < W ∧ W < ⊤} ≃o {U : Submodule R M // ⊥ < U ∧ U < p} := by
  classical
  refine (OrderIso.subtypeCongr (Submodule.mapIic p)
    (fun W => ⊥ < W ∧ W < ⊤)
    (fun U : Set.Iic p => ⊥ < (U : Submodule R M) ∧ (U : Submodule R M) < p) ?_).trans ?_
  · intro W
    have hb : (Submodule.mapIic p) ⊥ = ⟨⊥, Set.mem_Iic.2 bot_le⟩ := OrderIso.map_bot _
    have ht : (Submodule.mapIic p) ⊤ = ⟨p, Set.self_mem_Iic⟩ := OrderIso.map_top _
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have hlt := (Submodule.mapIic p).lt_iff_lt.2 h1
        rw [hb] at hlt
        exact hlt
      · have hlt := (Submodule.mapIic p).lt_iff_lt.2 h2
        rw [ht] at hlt
        exact hlt
    · rintro ⟨h1, h2⟩
      constructor
      · refine (Submodule.mapIic p).lt_iff_lt.1 ?_
        rw [hb]
        exact h1
      · refine (Submodule.mapIic p).lt_iff_lt.1 ?_
        rw [ht]
        exact h2
  · exact
      { toFun := fun U => ⟨(U.1 : Submodule R M), U.2⟩
        invFun := fun U => ⟨⟨U.1, Set.mem_Iic.2 (le_of_lt U.2.2)⟩, U.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }

/-- **The lower link has the homology of the building of the subspace.** -/
noncomputable def lowerLinkHomologyIso (p : Submodule R M) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (Rc : C) (n : ℕ) :
    (nerveFunctor.obj (Cat.of {U : Submodule R M // ⊥ < U ∧ U < p})).homology Rc n
      ≅ (nerveFunctor.obj
        (Cat.of {W : Submodule R (p : Type u) // ⊥ < W ∧ W < ⊤})).homology Rc n :=
  homologyIsoOfIso (orderIsoNerveIso (lowerLinkOrderIso p).symm) Rc n

end GaloisForLFunctions.HTGeometry
