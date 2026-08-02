import Mathlib.Algebra.Homology.AlternatingConst
import GaloisForLFunctions.HTGeometry.HomotopyEquivFunctor

/-!
# The singular chains of a contractible space are the coefficient object

The singular chain complex of a point is the alternating constant complex on the coefficient object,
and the alternating constant complex is chain homotopy equivalent to the complex concentrated in
degree zero.  Composing with the chain homotopy equivalence of a contractible space with a point
gives a split equivalence of the singular chains of a contractible space with the coefficient object
placed in degree zero.

Any additive coefficient functor carries this equivalence along, since it commutes with the
degree-zero complex.  In particular, tensoring the singular chains of the contractible unit sphere
of `ℓ²(ℕ, ℝ)` with a fixed module returns that module — the contraction with coefficients, as a
continuous chain homotopy equivalence rather than a bare homology isomorphism.

* `singularChainHomotopyEquivSingleOfPoint` : the chains of a point are the coefficient object.
* `singularChainHomotopyEquivSingle` : **the chains of a contractible space are the coefficient
  object in degree zero.**
* `singularChainCoeffHomotopyEquivSingle` : **the same after any additive coefficient functor.**
* `singularChainTensorHomotopyEquivSingle_sphere_lp` : the contraction tensored with a module.
* `singularChainUnitTensorHomotopyEquiv_sphere_lp` : **the chains of the `ℓ²`-sphere with unit
  coefficients, tensored with `A`, are `A`.**
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace GaloisForLFunctions

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{0} C] [HasZeroObject C]

/-! ## The chains of a point -/

/-- The singular chain complex of a point is chain homotopy equivalent to the coefficient object
placed in degree zero: it is the alternating constant complex on the coproduct of one copy of the
coefficient object. -/
def singularChainHomotopyEquivSingleOfPoint (R : C) :
    HomotopyEquiv (((singularChainComplexFunctor C).obj R).obj (TopCat.of Unit))
      ((ChainComplex.single₀ C).obj R) :=
  (HomotopyEquiv.ofIso
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R (TopCat.of Unit))).trans
    ((ChainComplex.alternatingConstHomotopyEquiv _).trans
      (HomotopyEquiv.ofIso ((ChainComplex.single₀ C).mapIso (coproductUniqueIso _))))

/-! ## The chains of a contractible space -/

/-- **The singular chains of a contractible space are chain homotopy equivalent to the coefficient
object placed in degree zero.** -/
def singularChainHomotopyEquivSingle (X : TopCat.{0}) [ContractibleSpace X] (R : C) :
    HomotopyEquiv (((singularChainComplexFunctor C).obj R).obj X)
      ((ChainComplex.single₀ C).obj R) :=
  (singularChainHomotopyEquivPoint X R).trans (singularChainHomotopyEquivSingleOfPoint R)

/-- The angular contraction in its sharpest chain form: the singular chains of the unit sphere of
`ℓ²(ℕ, ℝ)` are chain homotopy equivalent to the coefficient object in degree zero. -/
def singularChainHomotopyEquivSingle_sphere_lp (R : C) :
    HomotopyEquiv
      (((singularChainComplexFunctor C).obj R).obj
        (TopCat.of (Metric.sphere (0 : LpTwo) 1)))
      ((ChainComplex.single₀ C).obj R) :=
  letI : ContractibleSpace (Metric.sphere (0 : LpTwo) 1) := contractibleSpace_sphere_lp
  singularChainHomotopyEquivSingle (TopCat.of (Metric.sphere (0 : LpTwo) 1)) R

/-! ## Coefficients -/

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]

/-- **The contraction survives any additive coefficient functor**: applying an additive functor to
the singular chains of a contractible space gives a complex chain homotopy equivalent to the image
of the coefficient object, placed in degree zero. -/
def singularChainCoeffHomotopyEquivSingle (X : TopCat.{0}) [ContractibleSpace X] (R : C)
    (F : C ⥤ D) [F.Additive] :
    HomotopyEquiv
      ((F.mapHomologicalComplex _).obj (((singularChainComplexFunctor C).obj R).obj X))
      ((ChainComplex.single₀ D).obj (F.obj R)) :=
  (homotopyEquivMapOfAdditive (singularChainHomotopyEquivSingle X R) F).trans
    (HomotopyEquiv.ofIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app R))

/-- **The contraction of the `ℓ²`-sphere tensored with a module**: the singular chains of the
sphere with coefficients in `R`, tensored with `A`, are chain homotopy equivalent to `R ⊗ A` placed
in degree zero. -/
def singularChainTensorHomotopyEquivSingle_sphere_lp (R A : ModuleCat.{0} ℂ) :
    HomotopyEquiv
      (((MonoidalCategory.tensorRight A).mapHomologicalComplex _).obj
        (((singularChainComplexFunctor (ModuleCat.{0} ℂ)).obj R).obj
          (TopCat.of (Metric.sphere (0 : LpTwo) 1))))
      ((ChainComplex.single₀ (ModuleCat.{0} ℂ)).obj (R ⊗ A)) :=
  letI : ContractibleSpace (Metric.sphere (0 : LpTwo) 1) := contractibleSpace_sphere_lp
  singularChainCoeffHomotopyEquivSingle (TopCat.of (Metric.sphere (0 : LpTwo) 1)) R
    (MonoidalCategory.tensorRight A)

/-- **The angular contraction with coefficients**: the singular chains of the unit sphere of
`ℓ²(ℕ, ℝ)` with unit coefficients, tensored with a module `A`, are chain homotopy equivalent to `A`
placed in degree zero.  This is a split chain homotopy equivalence, not merely a homology
isomorphism. -/
def singularChainUnitTensorHomotopyEquiv_sphere_lp (A : ModuleCat.{0} ℂ) :
    HomotopyEquiv
      (((MonoidalCategory.tensorRight A).mapHomologicalComplex _).obj
        (((singularChainComplexFunctor (ModuleCat.{0} ℂ)).obj (𝟙_ (ModuleCat.{0} ℂ))).obj
          (TopCat.of (Metric.sphere (0 : LpTwo) 1))))
      ((ChainComplex.single₀ (ModuleCat.{0} ℂ)).obj A) :=
  (singularChainTensorHomotopyEquivSingle_sphere_lp (𝟙_ (ModuleCat.{0} ℂ)) A).trans
    (HomotopyEquiv.ofIso ((ChainComplex.single₀ (ModuleCat.{0} ℂ)).mapIso (λ_ A)))

end GaloisForLFunctions

end
