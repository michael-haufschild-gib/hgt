import GaloisForLFunctions.HTGeometry.SingularFunctoriality
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.Topology.Homotopy.TopCat.ToSSet
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Homotopy invariance of singular homology

The singular simplices used here — continuous maps from `stdSimplex ℝ (Fin (n+1))` — differ from
mathlib's only by a universe lift, and the identification is compatible with the faces.  The free
module simplicial object on either of them therefore has the same alternating face map complex up to
a canonical isomorphism, natural in the space.

A homotopy of continuous maps gives a homotopy of the induced maps of singular simplicial sets, hence
a simplicial homotopy, hence — after applying the free module functor and the alternating face map
complex — a chain homotopy.  Transporting along the isomorphism, homotopic maps induce the same map
on the homology of the concrete singular chain complex.
-/

open CategoryTheory Simplicial Opposite AlgebraicTopology

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R]

/-- The free module functor, with the index type and the ring in different universes. -/
noncomputable def freeMod : Type v ⥤ ModuleCat.{v} R where
  obj α := ModuleCat.of R (α →₀ R)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain R R f)
  map_id α := by
    refine ModuleCat.hom_ext ?_
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact Finsupp.lmapDomain_id R R
  map_comp f g := by
    refine ModuleCat.hom_ext ?_
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact Finsupp.lmapDomain_comp R R f g

variable {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The singular simplicial object of a space in mathlib's model. -/
noncomputable abbrev topSimplicial (X : Type v) [TopologicalSpace X] :
    SimplicialObject (ModuleCat.{v} R) :=
  (TopCat.toSSet.obj (TopCat.of X)) ⋙ freeMod R

/-- The two models of the singular simplicial object agree. -/
noncomputable def singSimplicialIso (X : Type v) [TopologicalSpace X] :
    topSimplicial R X ≅ singSimplicial R X :=
  NatIso.ofComponents
    (fun n => (freeMod R).mapIso (Equiv.toIso ((TopCat.of X).toSSetObjEquiv n)))
    (by
      intro n m f
      refine ModuleCat.hom_ext ?_
      show Finsupp.lmapDomain R R _ ∘ₗ Finsupp.lmapDomain R R _
        = Finsupp.lmapDomain R R _ ∘ₗ Finsupp.lmapDomain R R _
      rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
      congr 1)

/-- The map of singular simplicial objects induced by a continuous map. -/
noncomputable def singSimplicialMap (f : C(Y, X)) : singSimplicial R Y ⟶ singSimplicial R X where
  app n := ModuleCat.ofHom (singMapHom R f n.unop.len)
  naturality := by
    intro n m g
    refine ModuleCat.hom_ext ?_
    show Finsupp.lmapDomain R R _ ∘ₗ Finsupp.lmapDomain R R _
      = Finsupp.lmapDomain R R _ ∘ₗ Finsupp.lmapDomain R R _
    rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
    congr 1

theorem singMap_eq_map (f : C(Y, X)) :
    singMap R f = (alternatingFaceMapComplex (ModuleCat.{v} R)).map (singSimplicialMap R f) :=
  HomologicalComplex.hom_ext _ _ fun _ => rfl

theorem singSimplicialIso_naturality (f : C(Y, X)) :
    (singSimplicialIso R Y).hom ≫ singSimplicialMap R f
      = Functor.whiskerRight (TopCat.toSSet.map (TopCat.ofHom f)) (freeMod R)
        ≫ (singSimplicialIso R X).hom := by
  refine NatTrans.ext (funext fun n => ?_)
  refine ModuleCat.hom_ext ?_
  show Finsupp.lmapDomain R R _ ∘ₗ Finsupp.lmapDomain R R _
    = Finsupp.lmapDomain R R _ ∘ₗ Finsupp.lmapDomain R R _
  rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
  congr 1

/-- The isomorphism of chain complexes between the two models. -/
noncomputable def singChainComplexIso (X : Type v) [TopologicalSpace X] :
    (alternatingFaceMapComplex (ModuleCat.{v} R)).obj (topSimplicial R X) ≅ singChainComplex R X :=
  (alternatingFaceMapComplex (ModuleCat.{v} R)).mapIso (singSimplicialIso R X)

theorem singChainComplexIso_naturality (f : C(Y, X)) :
    (singChainComplexIso R Y).hom ≫ singMap R f
      = (alternatingFaceMapComplex (ModuleCat.{v} R)).map
          (Functor.whiskerRight (TopCat.toSSet.map (TopCat.ofHom f)) (freeMod R))
        ≫ (singChainComplexIso R X).hom := by
  have h := congrArg (alternatingFaceMapComplex (ModuleCat.{v} R)).map
    (singSimplicialIso_naturality R f)
  rw [Functor.map_comp, Functor.map_comp] at h
  rw [singMap_eq_map, singChainComplexIso, singChainComplexIso, Functor.mapIso_hom,
    Functor.mapIso_hom]
  exact h

/-- **Homotopy invariance.**  Homotopic maps induce the same map on singular homology. -/
theorem homologyMap_singMap_eq_of_homotopy {f g : C(Y, X)} (H : ContinuousMap.Homotopy f g)
    (n : ℕ) :
    HomologicalComplex.homologyMap (singMap R f) n
      = HomologicalComplex.homologyMap (singMap R g) n := by
  have hH : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := H
  have hchain := ((hH.toSSet.toSimplicialObjectHomotopy.whiskerRight
    (freeMod R)).toChainHomotopy).homologyMap_eq n
  have hchain' : HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{v} R)).map
        (Functor.whiskerRight (TopCat.toSSet.map (TopCat.ofHom f)) (freeMod R))) n
      = HomologicalComplex.homologyMap
        ((alternatingFaceMapComplex (ModuleCat.{v} R)).map
          (Functor.whiskerRight (TopCat.toSSet.map (TopCat.ofHom g)) (freeMod R))) n := hchain
  have hf := singChainComplexIso_naturality R f
  have hg := singChainComplexIso_naturality R g
  have key : HomologicalComplex.homologyMap ((singChainComplexIso R Y).hom ≫ singMap R f) n
      = HomologicalComplex.homologyMap ((singChainComplexIso R Y).hom ≫ singMap R g) n := by
    rw [hf, hg, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, hchain']
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at key
  haveI : IsIso (HomologicalComplex.homologyMap (singChainComplexIso R Y).hom n) :=
    inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
      (ComplexShape.down ℕ) n).map (singChainComplexIso R Y).hom))
  exact (cancel_epi (HomologicalComplex.homologyMap (singChainComplexIso R Y).hom n)).mp key

end GaloisForLFunctions.HTGeometry
