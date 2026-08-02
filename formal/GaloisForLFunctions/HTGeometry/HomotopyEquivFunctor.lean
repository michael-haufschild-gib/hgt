import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import GaloisForLFunctions.HTGeometry.SingularChainContractible

/-!
# Coefficients of a chain homotopy equivalence

An additive functor carries a chain homotopy equivalence to a chain homotopy equivalence: it carries
the two chain homotopies along, and functoriality identifies the composites.  In particular the
angular contraction survives any additive coefficient functor — for instance tensoring with a fixed
module.

This is the algebraic content of the extension of the contraction to coefficients: the chains of the
sphere with any coefficient functor applied stay chain-homotopy equivalent to those of a point.

* `homotopyEquivMapOfAdditive` : **additive functors preserve chain homotopy equivalences.**
* `singularChainHomotopyEquivPointMap` : the contraction survives a coefficient functor.
* `singularChainTensorHomotopyEquiv_sphere_lp` : the contraction after tensoring with a module.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace GaloisForLFunctions

/-- **An additive functor carries a chain homotopy equivalence to a chain homotopy
equivalence.** -/
def homotopyEquivMapOfAdditive {ι : Type*} {c : ComplexShape ι} {V W : Type*} [Category V]
    [Preadditive V] [Category W] [Preadditive W] {K L : HomologicalComplex V c}
    (e : HomotopyEquiv K L) (F : V ⥤ W) [F.Additive] :
    HomotopyEquiv ((F.mapHomologicalComplex c).obj K) ((F.mapHomologicalComplex c).obj L) where
  hom := (F.mapHomologicalComplex c).map e.hom
  inv := (F.mapHomologicalComplex c).map e.inv
  homotopyHomInvId := by
    refine (Homotopy.ofEq ?_).trans
      ((F.mapHomotopy e.homotopyHomInvId).trans (Homotopy.ofEq ?_))
    · rw [← Functor.map_comp]
    · exact CategoryTheory.Functor.map_id _ _
  homotopyInvHomId := by
    refine (Homotopy.ofEq ?_).trans
      ((F.mapHomotopy e.homotopyInvHomId).trans (Homotopy.ofEq ?_))
    · rw [← Functor.map_comp]
    · exact CategoryTheory.Functor.map_id _ _

/-- **The angular contraction survives an additive coefficient functor.** -/
def singularChainHomotopyEquivPointMap (X : TopCat.{0}) [ContractibleSpace X] {C D : Type*}
    [Category C] [Preadditive C] [HasCoproducts.{0} C] [Category D] [Preadditive D]
    (R : C) (F : C ⥤ D) [F.Additive] :
    HomotopyEquiv
      ((F.mapHomologicalComplex _).obj (((singularChainComplexFunctor C).obj R).obj X))
      ((F.mapHomologicalComplex _).obj
        (((singularChainComplexFunctor C).obj R).obj (TopCat.of Unit))) :=
  homotopyEquivMapOfAdditive (singularChainHomotopyEquivPoint X R) F

/-- **The contraction after tensoring with a module**: the singular chains of the unit sphere of
`ℓ²(ℕ, ℝ)`, tensored with a fixed module, stay chain-homotopy equivalent to the chains of a
point. -/
def singularChainTensorHomotopyEquiv_sphere_lp (R A : ModuleCat.{0} ℂ) :
    HomotopyEquiv
      (((MonoidalCategory.tensorRight A).mapHomologicalComplex _).obj
        (((singularChainComplexFunctor (ModuleCat.{0} ℂ)).obj R).obj
          (TopCat.of (Metric.sphere (0 : LpTwo) 1))))
      (((MonoidalCategory.tensorRight A).mapHomologicalComplex _).obj
        (((singularChainComplexFunctor (ModuleCat.{0} ℂ)).obj R).obj (TopCat.of Unit))) :=
  letI : ContractibleSpace (Metric.sphere (0 : LpTwo) 1) := contractibleSpace_sphere_lp
  singularChainHomotopyEquivPointMap (TopCat.of (Metric.sphere (0 : LpTwo) 1)) R
    (MonoidalCategory.tensorRight A)

end GaloisForLFunctions

end
