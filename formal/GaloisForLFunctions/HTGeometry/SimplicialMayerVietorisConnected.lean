import GaloisForLFunctions.HTGeometry.SimplicialMayerVietorisMono

/-!
# The union of two connected pieces meeting in a vertex is connected

Connectedness in the homological sense — that the constant map at a vertex acts as the identity on
degree-zero homology — passes to a union of two subcomplexes that share a vertex.

The Mayer--Vietoris sequence over the union is short exact in every degree, and in degree zero the
chain complex has nothing below it, so the map from the biproduct of the two pieces onto the union
is an epimorphism on homology.  Precomposing the difference of the constant map and the identity
with that epimorphism kills it, one summand at a time, because a constant map at a shared vertex
factors through each piece.

This is the input the Mayer--Vietoris vanishing needs in degree one, where the vanishing form of the
argument is unavailable: there the intersection of two pieces has nonvanishing degree-zero homology,
and what the argument needs instead is that this homology injects — which connectedness supplies.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X : SSet.{w}) (R : C) (A B : X.Subcomplex)

/-- **In degree zero the Mayer--Vietoris map onto the union is an epimorphism on homology.**  There
is no degree below zero for the connecting map to land in. -/
theorem epi_homologyMap_mvSupChainSnd_zero :
    Epi (HomologicalComplex.homologyMap (mvSupChainSnd X R A B) 0) := by
  have hepi : Epi ((mvSupChainSnd X R A B).f 0) :=
    (ShortComplex.shortExact_of_iso (mvSupChainShortComplexIso X R A B 0)
      (mvSupShortExact R _ _)).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 (fun j hj => by simp at hj)

variable {X A B}

/-- The vertex of a piece underlying a vertex of the intersection. -/
noncomputable def infVertexLeft (p : ((A ⊓ B : X.Subcomplex) : SSet.{w}) _⦋0⦌) :
    ((A : X.Subcomplex) : SSet.{w}) _⦋0⦌ :=
  (ConcreteCategory.hom
    ((SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)).app (op ⦋0⦌))) p

/-- The vertex of the other piece underlying a vertex of the intersection. -/
noncomputable def infVertexRight (p : ((A ⊓ B : X.Subcomplex) : SSet.{w}) _⦋0⦌) :
    ((B : X.Subcomplex) : SSet.{w}) _⦋0⦌ :=
  (ConcreteCategory.hom
    ((SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)).app (op ⦋0⦌))) p

/-- The vertex of the union underlying a vertex of the intersection. -/
noncomputable def supVertex (p : ((A ⊓ B : X.Subcomplex) : SSet.{w}) _⦋0⦌) :
    ((A ⊔ B : X.Subcomplex) : SSet.{w}) _⦋0⦌ :=
  (ConcreteCategory.hom
    ((SSet.Subcomplex.homOfLE ((inf_le_left : A ⊓ B ≤ A).trans le_sup_left)).app (op ⦋0⦌))) p

theorem const_supVertex_left (p : ((A ⊓ B : X.Subcomplex) : SSet.{w}) _⦋0⦌) :
    SSet.const (X := ((A : X.Subcomplex) : SSet.{w}))
        (Y := ((A : X.Subcomplex) : SSet.{w})) (infVertexLeft p)
      ≫ SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)
      = SSet.const (X := ((A : X.Subcomplex) : SSet.{w}))
        (Y := ((A ⊔ B : X.Subcomplex) : SSet.{w})) (supVertex p) := by
  rw [SSet.const_comp]
  rfl

theorem const_supVertex_right (p : ((A ⊓ B : X.Subcomplex) : SSet.{w}) _⦋0⦌) :
    SSet.const (X := ((B : X.Subcomplex) : SSet.{w}))
        (Y := ((B : X.Subcomplex) : SSet.{w})) (infVertexRight p)
      ≫ SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)
      = SSet.const (X := ((B : X.Subcomplex) : SSet.{w}))
        (Y := ((A ⊔ B : X.Subcomplex) : SSet.{w})) (supVertex p) := by
  rw [SSet.const_comp]
  rfl

variable (X A B)

/-- **Connectedness is preserved by unions along a vertex.**  If the two pieces are homologically
constant at a common vertex in degree zero, so is their union. -/
theorem homologyMap_const_eq_id_of_sup (p : ((A ⊓ B : X.Subcomplex) : SSet.{w}) _⦋0⦌)
    (hA : SSet.homologyMap (SSet.const (X := ((A : X.Subcomplex) : SSet.{w}))
      (Y := ((A : X.Subcomplex) : SSet.{w})) (infVertexLeft p)) R 0 = 𝟙 _)
    (hB : SSet.homologyMap (SSet.const (X := ((B : X.Subcomplex) : SSet.{w}))
      (Y := ((B : X.Subcomplex) : SSet.{w})) (infVertexRight p)) R 0 = 𝟙 _) :
    SSet.homologyMap (SSet.const (X := ((A ⊔ B : X.Subcomplex) : SSet.{w}))
      (Y := ((A ⊔ B : X.Subcomplex) : SSet.{w})) (supVertex p)) R 0 = 𝟙 _ := by
  haveI := epi_homologyMap_mvSupChainSnd_zero X R A B
  refine sub_eq_zero.1 (zero_of_epi_comp
    (HomologicalComplex.homologyMap (mvSupChainSnd X R A B) 0) ?_)
  have hgen : ∀ (D : X.Subcomplex) (hD : D ≤ A ⊔ B) (q : ((D : X.Subcomplex) : SSet.{w}) _⦋0⦌),
      SSet.homologyMap (SSet.const (X := ((D : X.Subcomplex) : SSet.{w}))
        (Y := ((D : X.Subcomplex) : SSet.{w})) q) R 0 = 𝟙 _ →
      SSet.const (X := ((D : X.Subcomplex) : SSet.{w}))
          (Y := ((D : X.Subcomplex) : SSet.{w})) q ≫ SSet.Subcomplex.homOfLE hD
        = SSet.const (X := ((D : X.Subcomplex) : SSet.{w}))
          (Y := ((A ⊔ B : X.Subcomplex) : SSet.{w})) (supVertex p) →
      SSet.homologyMap (SSet.Subcomplex.homOfLE hD) R 0
        ≫ (SSet.homologyMap (SSet.const (X := ((A ⊔ B : X.Subcomplex) : SSet.{w}))
          (Y := ((A ⊔ B : X.Subcomplex) : SSet.{w})) (supVertex p)) R 0 - 𝟙 _) = 0 := by
    intro D hD q hqid hq
    rw [Preadditive.comp_sub, Category.comp_id, ← SSet.homologyMap_comp, SSet.comp_const, ← hq,
      SSet.homologyMap_comp, hqid, Category.id_comp, sub_self]
  have hA0 := hgen A le_sup_left (infVertexLeft p) hA (const_supVertex_left p)
  have hB0 := hgen B le_sup_right (infVertexRight p) hB (const_supVertex_right p)
  rw [mvSupChainSnd, biprod.desc_eq, HomologicalComplex.homologyMap_add, Preadditive.add_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, Category.assoc,
    Category.assoc, HomologicalComplex.homologyMap_neg, Preadditive.neg_comp, hA0, hB0,
    neg_zero, comp_zero, comp_zero, add_zero]

end

end GaloisForLFunctions.HTGeometry
