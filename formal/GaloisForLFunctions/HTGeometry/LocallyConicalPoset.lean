import GaloisForLFunctions.HTGeometry.NerveHomotopy

/-!
# A poset that is conical on each component has no homology in positive degrees

A conically contractible poset has a monotone map dominating both the identity and a constant.  If
instead the dominated map is only *locally* constant — constant on comparable pairs, so constant on
each connected component — the same two homotopies still identify the identity on homology with that
map, and that map factors through the same poset with the discrete order.  An order complex of a
discrete poset has no simplices above dimension zero, so the homology vanishes above degree zero,
and the identity is zero there.

This is the form the disjoint union of a family of cones takes: there is no global cone point, only
one per component.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u

variable {Q : Type u} [Preorder Q]

/-- A type with the discrete order: only equal elements are comparable. -/
def discretePoset (Q : Type u) : Type u := Q

instance : PartialOrder (discretePoset Q) where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ hab hbc := hab.trans hbc
  le_antisymm _ _ hab _ := hab

omit [Preorder Q] in
theorem discretePoset_le_iff {a b : discretePoset Q} : a ≤ b ↔ a = b := Iff.rfl

omit [Preorder Q] in
/-- **A discrete order complex has no simplices above dimension zero.** -/
theorem hasDimensionLT_nerve_discretePoset :
    SSet.HasDimensionLT (nerveFunctor.obj (Cat.of (discretePoset Q))) 1 := by
  refine hasDimensionLT_nerve_of_chain_bound 1 (fun n f hf => ?_)
  by_contra hcon
  have hn : 0 < n := by omega
  have hlt : f ⟨0, by omega⟩ < f ⟨1, by omega⟩ := hf (by simp [Fin.lt_def])
  exact absurd (le_antisymm (le_of_lt hlt) (le_of_eq (discretePoset_le_iff.1 (le_of_lt hlt)).symm))
    (ne_of_lt hlt)

omit [Preorder Q] in
/-- **The homology of a discrete order complex vanishes in positive degrees.** -/
theorem isZero_homology_nerve_discretePoset {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    (hn : 1 ≤ n) :
    Limits.IsZero ((nerveFunctor.obj (Cat.of (discretePoset Q))).homology R n) :=
  haveI := hasDimensionLT_nerve_discretePoset (Q := Q)
  isZero_homology_of_hasDimensionLT _ 1 R n hn

/-- The projection to the discrete order, available whenever a monotone map is constant on
comparable pairs. -/
def toDiscrete (π : Q →o Q) (hconst : ∀ x y, x ≤ y → π x = π y) :
    Q →o discretePoset Q where
  toFun x := π x
  monotone' _ _ h := discretePoset_le_iff.2 (hconst _ _ h)

/-- The inclusion of the discrete order, which is monotone because nothing is comparable. -/
def fromDiscrete : discretePoset Q →o Q where
  toFun x := x
  monotone' _ _ h := le_of_eq (discretePoset_le_iff.1 h)

/-- **A dominated map acts as the identity on homology, in every degree.**  If a monotone map
dominates both the identity and another map, that other map is the identity on homology. -/
theorem homologyMap_nerve_eq_id_of_dominated (F π : Q →o Q) (hid : ∀ x, x ≤ F x)
    (hpt : ∀ x, π x ≤ F x)
    {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (n : ℕ) :
    SSet.homologyMap (nerveFunctor.map (Monotone.functor π.monotone).toCatHom) R n = 𝟙 _ := by
  have h₁ := (nerveHomotopyOfLE (OrderHom.id (α := Q)) F hid).congr_homologyMap R n
  have h₂ := (nerveHomotopyOfLE π F hpt).congr_homologyMap R n
  rw [show Monotone.functor (OrderHom.id (α := Q)).monotone = CategoryTheory.Functor.id Q from
      CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _),
    show (CategoryTheory.Functor.id Q).toCatHom = 𝟙 (Cat.of Q) from rfl,
    nerveFunctor.map_id] at h₁
  rw [h₂, ← h₁, SSet.homologyMap_id]

/-- **A locally conical poset has no homology in positive degrees.**  A monotone map dominating both
the identity and a map that is constant on comparable pairs makes the identity factor, on homology,
through the discrete order complex. -/
theorem isZero_homology_of_locally_conical (F π : Q →o Q) (hid : ∀ x, x ≤ F x)
    (hpt : ∀ x, π x ≤ F x) (hconst : ∀ x y, x ≤ y → π x = π y)
    {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (n : ℕ) (hn : 1 ≤ n) :
    Limits.IsZero ((nerveFunctor.obj (Cat.of Q)).homology R n) := by
  have h₁ := (nerveHomotopyOfLE (OrderHom.id (α := Q)) F hid).congr_homologyMap R n
  have h₂ := (nerveHomotopyOfLE π F hpt).congr_homologyMap R n
  rw [show Monotone.functor (OrderHom.id (α := Q)).monotone = CategoryTheory.Functor.id Q from
      CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _),
    show (CategoryTheory.Functor.id Q).toCatHom = 𝟙 (Cat.of Q) from rfl,
    nerveFunctor.map_id] at h₁
  have hfac : Monotone.functor π.monotone
      = (Monotone.functor (toDiscrete π hconst).monotone).comp
        (Monotone.functor (fromDiscrete (Q := Q)).monotone) :=
    CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)
  have hzero : SSet.homologyMap
      (nerveFunctor.map (Monotone.functor π.monotone).toCatHom) R n = 0 := by
    rw [hfac,
      show ((Monotone.functor (toDiscrete π hconst).monotone).comp
          (Monotone.functor (fromDiscrete (Q := Q)).monotone)).toCatHom
        = (Monotone.functor (toDiscrete π hconst).monotone).toCatHom
          ≫ (Monotone.functor (fromDiscrete (Q := Q)).monotone).toCatHom from rfl,
      nerveFunctor.map_comp, SSet.homologyMap_comp,
      (isZero_homology_nerve_discretePoset (Q := Q) R n hn).eq_zero_of_src
        (SSet.homologyMap (nerveFunctor.map
          (Monotone.functor (fromDiscrete (Q := Q)).monotone).toCatHom) R n),
      Limits.comp_zero]
  rw [Limits.IsZero.iff_id_eq_zero, ← SSet.homologyMap_id (X := nerveFunctor.obj (Cat.of Q))
    (R := R) n, h₁, ← h₂, hzero]

end GaloisForLFunctions.HTGeometry
