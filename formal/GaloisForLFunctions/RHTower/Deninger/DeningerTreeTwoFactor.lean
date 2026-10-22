import GaloisForLFunctions.RHTower.Deninger.DeningerHomologyAdditive

/-!
# The tree of cosets of a two factor amalgam

For an amalgamated free product of two groups, the edge and vertex sets of the tree of cosets are
disjoint unions of two, respectively three, coset spaces.  Combined with the identification of the
permutation representation on a disjoint union with a biproduct, this expresses the tree sequence
in terms of the cosets of the base group and of the two factors.

* `deningerEdgeEquivSum`, `deningerVertexEquivSum` : the equivariant decompositions.
* `deningerTreeEdgeRepIso`, `deningerTreeVertexRepIso` : the induced isomorphisms.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

variable {G : ULift.{u} Bool → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- The edges of the tree of a two factor amalgam are two copies of the cosets of the base
group. -/
def deningerEdgeEquivSum : DeningerTreeEdge φ ≃
    (PushoutI φ ⧸ (PushoutI.base φ).range) ⊕ (PushoutI φ ⧸ (PushoutI.base φ).range) where
  toFun e := cond e.idx.down (Sum.inl e.coset) (Sum.inr e.coset)
  invFun z := Sum.elim (fun x => ⟨ULift.up true, x⟩) (fun x => ⟨ULift.up false, x⟩) z
  left_inv e := by
    obtain ⟨⟨i⟩, x⟩ := e
    cases i <;> rfl
  right_inv z := by
    rcases z with x | x <;> rfl

theorem deningerEdgeEquivSum_smul (g : PushoutI φ) (e : DeningerTreeEdge φ) :
    deningerEdgeEquivSum (g • e) = g • deningerEdgeEquivSum e := by
  obtain ⟨⟨i⟩, x⟩ := e
  cases i <;> rfl

/-- The vertices of the tree of a two factor amalgam are the cosets of the base group together with
the cosets of the two factors. -/
def deningerVertexEquivSum : DeningerTreeVertex φ ≃
    (PushoutI φ ⧸ (PushoutI.base φ).range) ⊕
      ((PushoutI φ ⧸ (PushoutI.of (φ := φ) (ULift.up true)).range) ⊕
        (PushoutI φ ⧸ (PushoutI.of (φ := φ) (ULift.up false)).range)) where
  toFun v := match v with
    | .ofBase x => Sum.inl x
    | .ofSummand ⟨true⟩ y => Sum.inr (Sum.inl y)
    | .ofSummand ⟨false⟩ y => Sum.inr (Sum.inr y)
  invFun z := match z with
    | Sum.inl x => .ofBase x
    | Sum.inr (Sum.inl y) => .ofSummand (ULift.up true) y
    | Sum.inr (Sum.inr y) => .ofSummand (ULift.up false) y
  left_inv v := by
    cases v with
    | ofBase x => rfl
    | ofSummand i y => obtain ⟨i⟩ := i; cases i <;> rfl
  right_inv z := by
    rcases z with x | (y | y) <;> rfl

theorem deningerVertexEquivSum_smul (g : PushoutI φ) (v : DeningerTreeVertex φ) :
    deningerVertexEquivSum (g • v) = g • deningerVertexEquivSum v := by
  cases v with
  | ofBase x => rfl
  | ofSummand i y => obtain ⟨i⟩ := i; cases i <;> rfl

variable (k : Type u) [CommRing k]

/-- The edge representation of a two factor amalgam is two copies of the permutation representation
on the cosets of the base group. -/
noncomputable def deningerTreeEdgeRepIso :
    deningerTreeEdgeRep φ k ≅
      Rep.ofMulAction k (PushoutI φ) (PushoutI φ ⧸ (PushoutI.base φ).range) ⊞
        Rep.ofMulAction k (PushoutI φ) (PushoutI φ ⧸ (PushoutI.base φ).range) :=
  deningerPermRepIsoOfEquiv k deningerEdgeEquivSum deningerEdgeEquivSum_smul ≪≫
    deningerSumRepIso k

/-- The vertex representation of a two factor amalgam. -/
noncomputable def deningerTreeVertexRepIso :
    deningerTreeVertexRep φ k ≅
      Rep.ofMulAction k (PushoutI φ) (PushoutI φ ⧸ (PushoutI.base φ).range) ⊞
        (Rep.ofMulAction k (PushoutI φ)
            (PushoutI φ ⧸ (PushoutI.of (φ := φ) (ULift.up true)).range) ⊞
          Rep.ofMulAction k (PushoutI φ)
            (PushoutI φ ⧸ (PushoutI.of (φ := φ) (ULift.up false)).range)) :=
  deningerPermRepIsoOfEquiv k deningerVertexEquivSum deningerVertexEquivSum_smul ≪≫
    deningerSumRepIso k ≪≫ biprod.mapIso (Iso.refl _) (deningerSumRepIso k)

end RHTower
