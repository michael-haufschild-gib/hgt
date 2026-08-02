import GaloisForLFunctions.HTGeometry.SingularChainContractible

/-!
# Singular homology of a contractible space

Transporting the chain homotopy equivalence with a point along homology gives the acyclicity of a
contractible space: all higher singular homology vanishes, and in degree zero the homology is the
coproduct of one copy of the coefficient object.

Applied to the unit sphere of `ℓ²(ℕ, ℝ)` this is the homological form of the angular contraction:
the augmented chain complex of the sphere is acyclic.

* `isZero_singularHomology_of_contractible` : **higher singular homology of a contractible space
  vanishes.**
* `singularHomologyZeroIso_of_contractible` : the zeroth homology is the coefficient object.
* `isZero_singularHomology_sphere_lp` : the sphere of `ℓ²(ℕ, ℝ)` is acyclic.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

namespace GaloisForLFunctions

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{0} C]
variable [CategoryWithHomology C]

/-- **The higher singular homology of a contractible space vanishes.** -/
theorem isZero_singularHomology_of_contractible (X : TopCat.{0}) [ContractibleSpace X] (R : C)
    (n : ℕ) (hn : n ≠ 0) : IsZero (((singularHomologyFunctor C n).obj R).obj X) := by
  have e := singularChainHomotopyEquivPoint X R
  have hpoint : IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of Unit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R (TopCat.of Unit) hn
  exact IsZero.of_iso hpoint (e.toHomologyIso n)

/-- The zeroth singular homology of a contractible space is the coefficient object, presented as
the coproduct of one copy of it. -/
def singularHomologyZeroIso_of_contractible (X : TopCat.{0}) [ContractibleSpace X] (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun _ : (TopCat.of Unit) ↦ R :=
  (singularChainHomotopyEquivPoint X R).toHomologyIso 0 ≪≫
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace C R (TopCat.of Unit)

/-- **The unit sphere of `ℓ²(ℕ, ℝ)` is acyclic**: the homological form of the angular
contraction. -/
theorem isZero_singularHomology_sphere_lp (R : C) (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj
      (TopCat.of (Metric.sphere (0 : LpTwo) 1))) :=
  letI : ContractibleSpace (Metric.sphere (0 : LpTwo) 1) := contractibleSpace_sphere_lp
  isZero_singularHomology_of_contractible (TopCat.of (Metric.sphere (0 : LpTwo) 1)) R n hn

end GaloisForLFunctions

end
