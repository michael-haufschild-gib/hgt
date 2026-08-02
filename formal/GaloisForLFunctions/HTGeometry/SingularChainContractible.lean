import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import GaloisForLFunctions.HTGeometry.LpShift

/-!
# Singular chains of a contractible space

A homotopy equivalence of spaces induces a chain homotopy equivalence of singular chain complexes:
the prism operator of a homotopy is a chain homotopy, and functoriality turns the two homotopies of
a homotopy equivalence into the two chain homotopies.  For a contractible space the target is a
point, so the singular chain complex is chain-homotopy equivalent to the chain complex of a point —
a split equivalence, not merely a homology isomorphism.

Applied to the unit sphere of `ℓ²(ℕ, ℝ)`, whose contractibility was proved from the unilateral
shift, this is the angular contraction at the chain level.

* `singularChainHomotopyEquivOfHomotopyEquiv` : **homotopy equivalent spaces have chain-homotopy
  equivalent singular chains.**
* `singularChainHomotopyEquivPoint` : **the singular chains of a contractible space are
  chain-homotopy equivalent to those of a point.**
* `singularChainHomotopyEquivPoint_sphere_lp` : the angular contraction for the `ℓ²`-sphere.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

namespace GaloisForLFunctions

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts C]

/-- **A homotopy equivalence of spaces induces a chain homotopy equivalence of singular
chains.** -/
def singularChainHomotopyEquivOfHomotopyEquiv {X Y : TopCat} (e : ContinuousMap.HomotopyEquiv X Y)
    (R : C) :
    HomotopyEquiv (((singularChainComplexFunctor C).obj R).obj X)
      (((singularChainComplexFunctor C).obj R).obj Y) where
  hom := ((singularChainComplexFunctor C).obj R).map (TopCat.ofHom e.toFun)
  inv := ((singularChainComplexFunctor C).obj R).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    have h : TopCat.Homotopy (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) :=
      e.left_inv.some
    refine (Homotopy.ofEq ?_).trans
      ((h.singularChainComplexFunctorObjMap R).trans (Homotopy.ofEq ?_))
    · rw [← Functor.map_comp]
    · exact CategoryTheory.Functor.map_id _ _
  homotopyInvHomId := by
    have h : TopCat.Homotopy (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) :=
      e.right_inv.some
    refine (Homotopy.ofEq ?_).trans
      ((h.singularChainComplexFunctorObjMap R).trans (Homotopy.ofEq ?_))
    · rw [← Functor.map_comp]
    · exact CategoryTheory.Functor.map_id _ _

/-- **The singular chains of a contractible space are chain-homotopy equivalent to those of a
point.** -/
def singularChainHomotopyEquivPoint (X : TopCat) [ContractibleSpace X] (R : C) :
    HomotopyEquiv (((singularChainComplexFunctor C).obj R).obj X)
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of Unit)) :=
  singularChainHomotopyEquivOfHomotopyEquiv
    (X := X) (Y := TopCat.of Unit) (ContractibleSpace.hequiv_unit (X := X)).some R

/-- The angular contraction at the chain level: the singular chains of the unit sphere of
`ℓ²(ℕ, ℝ)` are chain-homotopy equivalent to those of a point. -/
def singularChainHomotopyEquivPoint_sphere_lp (R : C) :
    HomotopyEquiv
      (((singularChainComplexFunctor C).obj R).obj
        (TopCat.of (Metric.sphere (0 : LpTwo) 1)))
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of Unit)) :=
  letI : ContractibleSpace (Metric.sphere (0 : LpTwo) 1) := contractibleSpace_sphere_lp
  singularChainHomotopyEquivPoint (TopCat.of (Metric.sphere (0 : LpTwo) 1)) R

end GaloisForLFunctions

end
