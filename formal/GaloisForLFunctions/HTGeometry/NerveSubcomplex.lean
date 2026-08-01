import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Full subcomplexes of the nerve of a poset

A subset of a poset spans a full subcomplex of its nerve: the simplices all of whose vertices lie in
the subset.  Meets of such subcomplexes are spanned by intersections, and two subsets whose spanned
subcomplexes cover the nerve are exactly two subsets such that every chain lies entirely in one of
them.

This is the combinatorial side of a Mayer--Vietoris decomposition of an order complex.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

variable {P : Type u} [PartialOrder P]

/-- **The full subcomplex spanned by a subset of a poset**: the simplices all of whose vertices lie
in the subset. -/
def nerveSubcomplex (Q : Set P) : (nerve P).Subcomplex where
  obj _ := {x | ∀ i, x.obj i ∈ Q}
  map _ _ hx _ := hx _

@[simp] theorem mem_nerveSubcomplex {Q : Set P} {n : SimplexCategoryᵒᵖ}
    {x : (nerve P).obj n} :
    x ∈ (nerveSubcomplex Q).obj n ↔ ∀ i, x.obj i ∈ Q := Iff.rfl

/-- **Spanning is monotone.** -/
theorem nerveSubcomplex_mono {Q Q' : Set P} (h : Q ⊆ Q') :
    nerveSubcomplex Q ≤ nerveSubcomplex Q' :=
  fun _ _ hx i => h (hx i)

/-- **The meet of two full subcomplexes is spanned by the intersection.** -/
theorem nerveSubcomplex_inter (Q₁ Q₂ : Set P) :
    nerveSubcomplex (Q₁ ∩ Q₂) = nerveSubcomplex Q₁ ⊓ nerveSubcomplex Q₂ := by
  refine Subfunctor.ext (funext fun U => ?_)
  ext x
  exact ⟨fun hx => ⟨fun i => (hx i).1, fun i => (hx i).2⟩, fun hx i => ⟨hx.1 i, hx.2 i⟩⟩

/-- **Two subsets span a covering of the nerve exactly when every simplex lies entirely in one of
them.** -/
theorem nerveSubcomplex_sup_eq_top {Q₁ Q₂ : Set P}
    (h : ∀ (n : SimplexCategoryᵒᵖ) (x : (nerve P).obj n),
      (∀ i, x.obj i ∈ Q₁) ∨ (∀ i, x.obj i ∈ Q₂)) :
    nerveSubcomplex Q₁ ⊔ nerveSubcomplex Q₂ = ⊤ := by
  refine Subfunctor.ext (funext fun U => ?_)
  ext x
  exact ⟨fun _ => trivial, fun _ => h U x⟩

/-- **A minimal element's star and its complement span a covering.**  Every simplex either avoids the
element, or contains it and then lies in its star, because a vertex comparable to a minimal element
is above it. -/
theorem nerveSubcomplex_star_sup_compl (p : P) (hmin : ∀ q, q ≤ p → q = p) :
    nerveSubcomplex {q : P | p ≤ q} ⊔ nerveSubcomplex {q : P | q ≠ p} = ⊤ := by
  refine nerveSubcomplex_sup_eq_top (fun U x => ?_)
  by_cases hx : ∃ i, x.obj i = p
  · obtain ⟨i, hi⟩ := hx
    refine Or.inl (fun j => ?_)
    rcases le_total i j with hij | hij
    · exact hi ▸ leOfHom (x.map (homOfLE hij))
    · have := hmin (x.obj j) (hi ▸ leOfHom (x.map (homOfLE hij)))
      exact le_of_eq (hmin (x.obj j) (hi ▸ leOfHom (x.map (homOfLE hij)))).symm
  · exact Or.inr (fun j hj => hx ⟨j, hj⟩)

/-! ## The full subcomplex is the nerve of the subset -/

/-- **The full subcomplex spanned by a subset is the nerve of that subset**, so every statement
about the order complex of a subposet applies to it. -/
def nerveSubcomplexIso (Q : Set P) :
    (nerveSubcomplex Q : SSet.{u}) ≅ nerve (Q : Type u) :=
  NatIso.ofComponents
    (fun n => Equiv.toIso
      { toFun := fun x =>
          { obj := fun i => ⟨x.1.obj i, x.2 i⟩
            map := fun {_ _} f => homOfLE (leOfHom (x.1.map f)) }
        invFun := fun y =>
          ⟨{ obj := fun i => (y.obj i).1
             map := fun {_ _} f => homOfLE (leOfHom (y.map f)) }, fun i => (y.obj i).2⟩
        left_inv := fun x => Subtype.ext (CategoryTheory.Functor.ext (fun _ => rfl)
          (fun _ _ _ => Subsingleton.elim _ _))
        right_inv := fun y => CategoryTheory.Functor.ext (fun i => Subtype.ext rfl)
          (fun _ _ _ => Subsingleton.elim _ _) })
    (fun {_ _} _ => rfl)

/-- **A full subcomplex has the homology of the subposet it spans.** -/
noncomputable def nerveSubcomplexHomologyIso (Q : Set P) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (i : ℕ) :
    ((nerveSubcomplex Q : SSet.{u})).homology R i ≅ (nerve (Q : Type u)).homology R i :=
  (SSet.homologyFunctor R i).mapIso (nerveSubcomplexIso Q)

/-- **The full subcomplex spanned by the elements above a fixed one is contractible.**  It is the
nerve of a poset with a least element. -/
theorem isZero_homology_nerveSubcomplex_above (p : P) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (i : ℕ)
    (hi : Limits.IsZero ((nerve ({q : P | p ≤ q} : Type u)).homology R i)) :
    Limits.IsZero (((nerveSubcomplex {q : P | p ≤ q} : SSet.{u})).homology R i) :=
  Limits.IsZero.of_iso hi (nerveSubcomplexHomologyIso _ R i)

end GaloisForLFunctions.HTGeometry
