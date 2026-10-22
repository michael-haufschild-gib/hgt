import GaloisForLFunctions.RHTower.Deninger.DeningerTreeTwoFactor

/-!
# The homology of the tree modules of a two factor amalgam

Combining the decomposition of the edge and vertex representations into biproducts of permutation
representations with additivity of group homology and Shapiro's lemma, the homology of the tree
modules is the homology of the base group and of the two factors.

* `deningerTreeEdgeHomologyIso` : `Hₙ(G, k[E]) ≅ Hₙ(C, k) ⊞ Hₙ(C, k)`.
* `deningerTreeVertexHomologyIso` : `Hₙ(G, k[V]) ≅ Hₙ(C, k) ⊞ (Hₙ(A₀, k) ⊞ Hₙ(A₁, k))`.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

variable {G : ULift.{u} Bool → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} (k : Type u) [CommRing k] [DecidableEq (PushoutI φ)]

/-- The homology of the edge module is two copies of the homology of the base group. -/
noncomputable def deningerTreeEdgeHomologyIso (n : ℕ) :
    (groupHomology.functor k (PushoutI φ) n).obj (deningerTreeEdgeRep φ k) ≅
      groupHomology (Rep.trivial k ((PushoutI.base φ).range) k) n ⊞
        groupHomology (Rep.trivial k ((PushoutI.base φ).range) k) n :=
  (groupHomology.functor k (PushoutI φ) n).mapIso (deningerTreeEdgeRepIso k) ≪≫
    deningerHomologyBiprodIso _ _ n ≪≫
      biprod.mapIso (deningerPermutationShapiro (PushoutI.base φ).range n)
        (deningerPermutationShapiro (PushoutI.base φ).range n)

/-- The homology of the vertex module is the homology of the base group together with the homology
of the two factors. -/
noncomputable def deningerTreeVertexHomologyIso (n : ℕ) :
    (groupHomology.functor k (PushoutI φ) n).obj (deningerTreeVertexRep φ k) ≅
      groupHomology (Rep.trivial k ((PushoutI.base φ).range) k) n ⊞
        (groupHomology (Rep.trivial k ((PushoutI.of (φ := φ) (ULift.up true)).range) k) n ⊞
          groupHomology (Rep.trivial k ((PushoutI.of (φ := φ) (ULift.up false)).range) k) n) :=
  (groupHomology.functor k (PushoutI φ) n).mapIso (deningerTreeVertexRepIso k) ≪≫
    deningerHomologyBiprodIso _ _ n ≪≫
      biprod.mapIso (deningerPermutationShapiro (PushoutI.base φ).range n)
        (deningerHomologyBiprodIso _ _ n ≪≫
          biprod.mapIso
            (deningerPermutationShapiro (PushoutI.of (φ := φ) (ULift.up true)).range n)
            (deningerPermutationShapiro (PushoutI.of (φ := φ) (ULift.up false)).range n))

end RHTower
