import GaloisForLFunctions.HTGeometry.ShilovEnvelopeCorrelationPullback
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The simplicial boundary-join coefficient system

For a small diagram `F : C ⥤ ModuleCat 𝕜` of coefficient modules and a boundary submodule `J X`
at every object, every simplex of the nerve of `C` carries the module at its terminal vertex and
the join of all boundary submodules transported to that vertex.

This module proves that the join assignment is a coefficient system: it is carried into itself by
every simplex map, and it is the least such assignment whose vertex values contain the given
boundary submodules.  At a one-simplex the join is the edge join of the corresponding transport
map, and the degree-zero cocycle condition of the resulting quotient system is exactly membership
in the envelope correlation of that edge.

Main results:

* `simplexJoin_map_le`: the coefficient-system property;
* `simplexJoin_le_of_isCoefficientSystem`: minimality of the join system;
* `simplexJoin_zero`, `simplexJoin_one`: vertex and edge values;
* `edge_quotient_eq_iff_mem_envelopeCorrelation`: the degree-zero cocycle condition is exactly
  the envelope correlation of the edge.
-/

open CategoryTheory Opposite Simplicial

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]
variable {C : Type v} [Category.{v} C]

/-- Terminal vertex of a simplex of the nerve. -/
abbrev simplexTip {p : ℕ} (σ : ComposableArrows C p) : C := σ.obj (Fin.last p)

variable (F : C ⥤ ModuleCat.{v} 𝕜)

/-- Transport of the terminal coefficient along a simplex map. -/
noncomputable def simplexTransport {n m : SimplexCategory} (θ : n ⟶ m)
    (τ : ComposableArrows C m.len) :
    F.obj (simplexTip ((nerve C).map θ.op τ)) →ₗ[𝕜] F.obj (simplexTip τ) :=
  (F.map (τ.map (homOfLE
    (Fin.le_last (SimplexCategory.Hom.toOrderHom θ (Fin.last n.len)))))).hom

theorem simplexTransport_id {n : SimplexCategory} (τ : ComposableArrows C n.len) :
    simplexTransport F (𝟙 n) τ = LinearMap.id := by
  have h : τ.map (homOfLE (Fin.le_last
      (SimplexCategory.Hom.toOrderHom (𝟙 n) (Fin.last n.len)))) = 𝟙 _ := τ.map_id _
  show (F.map _).hom = LinearMap.id
  rw [h, F.map_id]
  rfl

theorem simplexTransport_comp {n m k : SimplexCategory} (θ : n ⟶ m) (ψ : m ⟶ k)
    (υ : ComposableArrows C k.len) :
    (simplexTransport F ψ υ).comp (simplexTransport F θ ((nerve C).map ψ.op υ)) =
      simplexTransport F (θ ≫ ψ) υ := by
  have hmor : ((nerve C).map ψ.op υ).map
        (homOfLE (Fin.le_last (SimplexCategory.Hom.toOrderHom θ (Fin.last n.len))))
      ≫ υ.map (homOfLE (Fin.le_last (SimplexCategory.Hom.toOrderHom ψ (Fin.last m.len))))
    = υ.map (homOfLE (Fin.le_last
        (SimplexCategory.Hom.toOrderHom (θ ≫ ψ) (Fin.last n.len)))) :=
    (υ.map_comp _ _).symm.trans (congrArg _ (Subsingleton.elim _ _))
  show ((F.map _).hom).comp ((F.map _).hom) = (F.map _).hom
  rw [← ModuleCat.hom_comp, ← F.map_comp]
  exact congrArg (fun g => ModuleCat.Hom.hom (F.map g)) hmor

/-- Transport of the coefficient at the `i`-th vertex of a simplex to its terminal vertex. -/
noncomputable def vertexTransport {p : ℕ} (σ : ComposableArrows C p) (i : Fin (p + 1)) :
    F.obj (σ.obj i) →ₗ[𝕜] F.obj (simplexTip σ) :=
  (F.map (σ.map (homOfLE (Fin.le_last i)))).hom

theorem vertexTransport_last {p : ℕ} (σ : ComposableArrows C p) :
    vertexTransport F σ (Fin.last p) = LinearMap.id := by
  have h : σ.map (homOfLE (Fin.le_last (Fin.last p))) = 𝟙 _ := σ.map_id _
  show (F.map _).hom = LinearMap.id
  rw [h, F.map_id]
  rfl

theorem simplexTransport_comp_vertexTransport {n m : SimplexCategory} (θ : n ⟶ m)
    (τ : ComposableArrows C m.len) (i : Fin (n.len + 1)) :
    (simplexTransport F θ τ).comp (vertexTransport F ((nerve C).map θ.op τ) i) =
      vertexTransport F τ (SimplexCategory.Hom.toOrderHom θ i) := by
  have hmor : ((nerve C).map θ.op τ).map (homOfLE (Fin.le_last i))
      ≫ τ.map (homOfLE (Fin.le_last (SimplexCategory.Hom.toOrderHom θ (Fin.last n.len))))
    = τ.map (homOfLE (Fin.le_last (SimplexCategory.Hom.toOrderHom θ i))) :=
    (τ.map_comp _ _).symm.trans (congrArg _ (Subsingleton.elim _ _))
  show ((F.map _).hom).comp ((F.map _).hom) = (F.map _).hom
  rw [← ModuleCat.hom_comp, ← F.map_comp]
  exact congrArg (fun g => ModuleCat.Hom.hom (F.map g)) hmor

variable (J : ∀ X : C, Submodule 𝕜 (F.obj X))

/-- Join of all vertex boundary submodules of a simplex, transported to its terminal vertex. -/
noncomputable def simplexJoin {p : ℕ} (σ : ComposableArrows C p) :
    Submodule 𝕜 (F.obj (simplexTip σ)) :=
  ⨆ i : Fin (p + 1), Submodule.map (vertexTransport F σ i) (J (σ.obj i))

theorem vertexJoin_le_simplexJoin {p : ℕ} (σ : ComposableArrows C p) (i : Fin (p + 1)) :
    Submodule.map (vertexTransport F σ i) (J (σ.obj i)) ≤ simplexJoin F J σ :=
  le_iSup (fun j : Fin (p + 1) => Submodule.map (vertexTransport F σ j) (J (σ.obj j))) i

theorem tip_boundary_le_simplexJoin {p : ℕ} (σ : ComposableArrows C p) :
    J (simplexTip σ) ≤ simplexJoin F J σ := by
  have h := vertexJoin_le_simplexJoin F J σ (Fin.last p)
  rwa [vertexTransport_last, Submodule.map_id] at h

/-- The join assignment is carried into itself by every simplex map. -/
theorem simplexJoin_map_le {n m : SimplexCategory} (θ : n ⟶ m)
    (τ : ComposableArrows C m.len) :
    Submodule.map (simplexTransport F θ τ) (simplexJoin F J ((nerve C).map θ.op τ)) ≤
      simplexJoin F J τ := by
  rw [simplexJoin, Submodule.map_iSup]
  refine iSup_le fun i => ?_
  rw [← Submodule.map_comp, simplexTransport_comp_vertexTransport]
  exact vertexJoin_le_simplexJoin F J τ (SimplexCategory.Hom.toOrderHom θ i)

/-- Assignments of submodules to simplices that are carried into themselves by every simplex
map. -/
def IsJoinCoefficientSystem
    (N : ∀ (p : ℕ), ∀ σ : ComposableArrows C p, Submodule 𝕜 (F.obj (simplexTip σ))) : Prop :=
  ∀ {n m : SimplexCategory} (θ : n ⟶ m) (τ : ComposableArrows C m.len),
    Submodule.map (simplexTransport F θ τ) (N n.len ((nerve C).map θ.op τ)) ≤ N m.len τ

theorem isJoinCoefficientSystem_simplexJoin :
    IsJoinCoefficientSystem F (fun _ σ => simplexJoin F J σ) :=
  fun θ τ => simplexJoin_map_le F J θ τ

/-- Simplex map that selects the `i`-th vertex of a `p`-simplex. -/
def vertexInclusion {p : ℕ} (i : Fin (p + 1)) : (⦋0⦌ : SimplexCategory) ⟶ ⦋p⦌ :=
  SimplexCategory.const _ _ i

theorem simplexTransport_vertexInclusion {p : ℕ} (σ : ComposableArrows C p)
    (i : Fin (p + 1)) :
    simplexTransport F (vertexInclusion i) σ = vertexTransport F σ i :=
  rfl

/-- Minimality: the join system is the least coefficient system whose vertex values contain the
prescribed boundary submodules. -/
theorem simplexJoin_le_of_isCoefficientSystem
    (N : ∀ (p : ℕ), ∀ σ : ComposableArrows C p, Submodule 𝕜 (F.obj (simplexTip σ)))
    (hN : IsJoinCoefficientSystem F N)
    (hvertex : ∀ σ : ComposableArrows C 0, J (simplexTip σ) ≤ N 0 σ)
    {p : ℕ} (σ : ComposableArrows C p) :
    simplexJoin F J σ ≤ N p σ := by
  refine iSup_le fun i => ?_
  have hmap := hN (vertexInclusion i) σ
  rw [simplexTransport_vertexInclusion] at hmap
  refine le_trans (Submodule.map_mono ?_) hmap
  exact hvertex ((nerve C).map (vertexInclusion i).op σ)

theorem simplexJoin_zero (σ : ComposableArrows C 0) :
    simplexJoin F J σ = J (simplexTip σ) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; omega)
    subst hi
    rw [vertexTransport_last, Submodule.map_id]
  · exact tip_boundary_le_simplexJoin F J σ

theorem simplexJoin_one (σ : ComposableArrows C 1) :
    simplexJoin F J σ =
      edgeJoin (vertexTransport F σ 0) (J (σ.obj 0)) (J (simplexTip σ)) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rcases (by have := i.isLt; omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h | h
    · have hi : i = 0 := Fin.ext h
      subst hi
      exact le_sup_right
    · have hi : i = Fin.last 1 := Fin.ext h
      subst hi
      rw [vertexTransport_last, Submodule.map_id]
      exact le_sup_left
  · exact sup_le (tip_boundary_le_simplexJoin F J σ) (vertexJoin_le_simplexJoin F J σ 0)

/-- The degree-zero cocycle condition of the quotient system at an edge is exactly membership in
the envelope correlation of that edge. -/
theorem edge_quotient_eq_iff_mem_envelopeCorrelation (σ : ComposableArrows C 1)
    (x : F.obj (σ.obj 0)) (y : F.obj (simplexTip σ)) :
    ((Submodule.Quotient.mk (vertexTransport F σ 0 x) :
        F.obj (simplexTip σ) ⧸ simplexJoin F J σ) = Submodule.Quotient.mk y) ↔
      (((Submodule.Quotient.mk x : F.obj (σ.obj 0) ⧸ J (σ.obj 0)),
        (Submodule.Quotient.mk y : F.obj (simplexTip σ) ⧸ J (simplexTip σ))) ∈
          envelopeCorrelation (vertexTransport F σ 0) (J (σ.obj 0)) (J (simplexTip σ))) := by
  rw [envelopeCorrelation_eq_correlationPullback, mem_correlationPullback_iff]
  show _ ↔ edgeProjSource (vertexTransport F σ 0) (J (σ.obj 0)) (J (simplexTip σ))
      (Submodule.Quotient.mk x) =
    edgeProjTarget (vertexTransport F σ 0) (J (σ.obj 0)) (J (simplexTip σ))
      (Submodule.Quotient.mk y)
  rw [edgeProjSource_mk, edgeProjTarget_mk, simplexJoin_one]

end BoundaryMigration
end GaloisForLFunctions.HTGeometry
