import GaloisForLFunctions.HTGeometry.SimplicialMayerVietoris
import GaloisForLFunctions.HTGeometry.CoproductMayerVietorisFamily

/-!
# The disjoint union of a family of subcomplexes

The pieces of a many-piece cover overlap, so their disjoint union is not a subcomplex of the ambient
simplicial set.  It is a simplicial set in its own right — degreewise the disjoint union of the
simplices of the pieces — together with a map to the ambient one, and that is the middle term of the
Mayer--Vietoris sequence of a cover with many pieces.

Its chains in degree `n` are, definitionally, the coproduct over the disjoint union of the pieces'
`n`-simplices, which is the object the coproduct Mayer--Vietoris sequence is stated for.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

variable {X : SSet.{w}} {ι : Type w}

/-- The disjoint union of a family of subcomplexes, as a simplicial set. -/
def famSSet (A : ι → X.Subcomplex) : SSet.{w} where
  obj n := Σ a : ι, ((A a : SSet.{w}).obj n)
  map f := ↾fun p => ⟨p.1, (A p.1 : SSet.{w}).map f p.2⟩
  map_id _ := by ext p <;> first | rfl | (simp; rfl)
  map_comp _ _ := by ext p <;> first | rfl | (simp; rfl)

@[simp] theorem famSSet_obj (A : ι → X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    (famSSet A).obj n = Σ a : ι, ((A a : SSet.{w}).obj n) := rfl

/-- The map from the disjoint union of a family to any subcomplex containing every member. -/
def famSSetHom (A : ι → X.Subcomplex) (B : X.Subcomplex) (h : ∀ a, A a ≤ B) :
    famSSet A ⟶ (B : SSet.{w}) where
  app n := ↾fun p => ⟨(p.2 : X.obj n), h p.1 _ p.2.2⟩
  naturality _ _ _ := rfl

/-- The map between disjoint unions of two families, member by member. -/
def famSSetMap {A A' : ι → X.Subcomplex} (h : ∀ a, A a ≤ A' a) : famSSet A ⟶ famSSet A' where
  app n := ↾fun p => ⟨p.1, ⟨(p.2 : X.obj n), h p.1 _ p.2.2⟩⟩
  naturality _ _ _ := rfl

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable (R : C)

/-- **The chains of a disjoint union are the coproduct over the disjoint union of the simplices.** -/
theorem famSSet_chainComplex_X (A : ι → X.Subcomplex) (n : ℕ) :
    ((famSSet A).chainComplex R).X n
      = famCoproduct R (fun a => (A a).obj (op ⦋n⦌)) := rfl

/-- **The chain map of the map to the ambient subcomplex is the map of coproducts.** -/
theorem chainComplexMap_famSSetHom_f (A : ι → X.Subcomplex) (B : X.Subcomplex)
    (h : ∀ a, A a ≤ B) (n : ℕ) :
    (SSet.chainComplexMap (famSSetHom A B h) R).f n
      = Sigma.desc (fun q : famIndex (fun a => (A a).obj (op ⦋n⦌)) =>
        Sigma.ι (fun _ : (B.obj (op ⦋n⦌) : Type w) => R) ⟨(q.2 : X.obj (op ⦋n⦌)), h q.1 _ q.2.2⟩) := by
  refine Sigma.hom_ext _ _ (fun q => ?_)
  refine (SSet.ι_chainComplexMap_f _ _ (famSSetHom A B h) R q).trans ?_
  exact (Sigma.ι_desc (fun q : famIndex (fun a => (A a).obj (op ⦋n⦌)) =>
    Sigma.ι (fun _ : (B.obj (op ⦋n⦌) : Type w) => R)
      ⟨(q.2 : X.obj (op ⦋n⦌)), h q.1 _ q.2.2⟩) q).symm

/-- **And the chain map of a map of families is the map of coproducts.** -/
theorem chainComplexMap_famSSetMap_f {A A' : ι → X.Subcomplex} (h : ∀ a, A a ≤ A' a) (n : ℕ) :
    (SSet.chainComplexMap (famSSetMap h) R).f n
      = Sigma.desc (fun q : famIndex (fun a => (A a).obj (op ⦋n⦌)) =>
        Sigma.ι (fun _ : famIndex (fun a => (A' a).obj (op ⦋n⦌)) => R)
          ⟨q.1, ⟨(q.2 : X.obj (op ⦋n⦌)), h q.1 _ q.2.2⟩⟩) := by
  refine Sigma.hom_ext _ _ (fun q => ?_)
  refine (SSet.ι_chainComplexMap_f _ _ (famSSetMap h) R q).trans ?_
  exact (Sigma.ι_desc (fun q : famIndex (fun a => (A a).obj (op ⦋n⦌)) =>
    Sigma.ι (fun _ : famIndex (fun a => (A' a).obj (op ⦋n⦌)) => R)
      ⟨q.1, ⟨(q.2 : X.obj (op ⦋n⦌)), h q.1 _ q.2.2⟩⟩) q).symm

end

/-- **A family of subcomplexes covers the simplices of its join, in every degree.** -/
theorem iSup_obj (A : ι → X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    (⨆ a, A a).obj n = ⋃ a, (A a).obj n := by
  ext x
  simp

/-- **The simplices of the join of a base with a family are covered by the pieces' simplices.** -/
theorem mem_base_iSup_obj (A₀ : X.Subcomplex) (A : ι → X.Subcomplex) (n : SimplexCategoryᵒᵖ)
    {x : X.obj n} (hx : x ∈ (A₀ ⊔ ⨆ a, A a).obj n) :
    x ∈ A₀.obj n ∨ ∃ a, x ∈ (A a).obj n := by
  rcases (show x ∈ A₀.obj n ∪ (⨆ a, A a).obj n from hx) with h₀ | hU
  · exact Or.inl h₀
  · exact Or.inr (by simpa [iSup_obj] using hU)

end GaloisForLFunctions.HTGeometry
