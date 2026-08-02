import GaloisForLFunctions.HTGeometry.FamilySimplicialSet
import GaloisForLFunctions.HTGeometry.NerveSubcomplex

/-!
# The disjoint union of full subcomplexes is the nerve of the disjoint union of the subposets

A family of subsets of a poset has a disjoint union poset — pairs `(a, x)` with `x` in the `a`-th
subset, ordered within each part and incomparable across parts.  Its order complex is the disjoint
union of the order complexes of the parts, because a chain in a disjoint union stays in one part:
comparable elements share their index.

This is what turns the middle term of the many-piece Mayer--Vietoris sequence — a disjoint union of
subcomplexes, which is not a subcomplex — back into an order complex, where the contractibility of
each piece can be used.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

variable {P : Type u} [PartialOrder P] {ι : Type u}

/-- The disjoint union of a family of subposets. -/
def famPoset (S : ι → Set P) : Type u := {q : ι × P // q.2 ∈ S q.1}

instance (S : ι → Set P) : PartialOrder (famPoset S) where
  le q q' := (Subtype.val q).1 = (Subtype.val q').1 ∧ (Subtype.val q).2 ≤ (Subtype.val q').2
  le_refl _ := ⟨rfl, le_rfl⟩
  le_trans _ _ _ hab hbc := ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  le_antisymm a b hab hba :=
    Subtype.ext (Prod.ext hab.1 (le_antisymm hab.2 hba.2))

theorem famPoset_le_iff {S : ι → Set P} {q q' : famPoset S} :
    q ≤ q' ↔ (Subtype.val q).1 = (Subtype.val q').1
      ∧ (Subtype.val q).2 ≤ (Subtype.val q').2 := Iff.rfl

/-- The index of a member of a chain in a disjoint union does not depend on the member. -/
theorem famPoset_index_eq {S : ι → Set P} {n : ℕ} (y : ComposableArrows (famPoset S) n)
    (i : Fin (n + 1)) :
    (Subtype.val (y.obj 0)).1 = (Subtype.val (y.obj i)).1 :=
  (famPoset_le_iff.1 (leOfHom (y.map (homOfLE (Fin.zero_le i))))).1

/-- **The disjoint union of the full subcomplexes spanned by a family of subsets is the order
complex of the disjoint union poset.** -/
def famPosetNerveIso (S : ι → Set P) :
    famSSet (fun a => nerveSubcomplex (S a)) ≅ nerve (famPoset S) :=
  NatIso.ofComponents
    (fun n => Equiv.toIso
      { toFun := fun p =>
          { obj := fun i => ⟨(p.1, (p.2 : (nerve P).obj n).obj i), p.2.2 i⟩
            map := fun {_ _} f => homOfLE ⟨rfl, leOfHom ((p.2 : (nerve P).obj n).map f)⟩ }
        invFun := fun y =>
          ⟨(Subtype.val (y.obj 0)).1,
            ⟨{ obj := fun i => (Subtype.val (y.obj i)).2
               map := fun {_ _} f => homOfLE (famPoset_le_iff.1 (leOfHom (y.map f))).2 },
             fun i => by
               have h := famPoset_index_eq y i
               exact h ▸ (y.obj i).2⟩⟩
        left_inv := fun p => by
          refine Sigma.ext rfl ?_
          refine heq_of_eq (Subtype.ext ?_)
          exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)
        right_inv := fun y =>
          CategoryTheory.Functor.ext
            (fun i => Subtype.ext (Prod.ext (famPoset_index_eq y i) rfl))
            (fun _ _ _ => Subsingleton.elim _ _) })
    (fun {_ _} _ => rfl)

/-- The projection of the disjoint union to the ambient poset. -/
def famPosetProj (S : ι → Set P) : famPoset S →o P where
  toFun q := (Subtype.val q).2
  monotone' _ _ h := (famPoset_le_iff.1 h).2

/-- A family inclusion induces a monotone map of the disjoint unions. -/
def famPosetMap {S S' : ι → Set P} (h : ∀ a, S a ⊆ S' a) : famPoset S →o famPoset S' where
  toFun q := ⟨Subtype.val q, h _ q.2⟩
  monotone' _ _ hq := famPoset_le_iff.2 (famPoset_le_iff.1 hq)

/-- **The identification is natural for the map to the ambient complex.** -/
theorem famPosetNerveIso_inv_comp_famSSetHom (S : ι → Set P) :
    (famPosetNerveIso S).inv ≫ famSSetHom (fun a => nerveSubcomplex (S a)) ⊤ (fun _ => le_top)
        ≫ (SSet.Subcomplex.topIso (nerve P)).hom
      = nerveFunctor.map (Monotone.functor (famPosetProj S).monotone).toCatHom := rfl

/-- **And for a map of families.** -/
theorem famPosetNerveIso_inv_comp_famSSetMap {S S' : ι → Set P} (h : ∀ a, S a ⊆ S' a) :
    (famPosetNerveIso S).inv ≫ famSSetMap (fun a => nerveSubcomplex_mono (h a))
        ≫ (famPosetNerveIso S').hom
      = nerveFunctor.map (Monotone.functor (famPosetMap h).monotone).toCatHom := by
  ext n y i
  apply Subtype.ext
  apply Prod.ext
  · show (Subtype.val (y.obj 0)).1 = (Subtype.val (y.obj i)).1
    exact famPoset_index_eq y i
  · rfl

/-- **And therefore the same homology.** -/
noncomputable def famPosetHomologyIso (S : ι → Set P) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (i : ℕ) :
    (famSSet (fun a => nerveSubcomplex (S a))).homology R i
      ≅ (nerve (famPoset S)).homology R i :=
  (SSet.homologyFunctor R i).mapIso (famPosetNerveIso S)

end GaloisForLFunctions.HTGeometry
