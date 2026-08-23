/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraInverseOpposite

/-!
# Inversion for cyclic `H²` Brauer representatives

The all-degree inverse-parameter opposite equivalence descends to every selected cyclic `H²`
Brauer representative.  Thus the cohomological negation operation agrees with Brauer inversion,
both before and after the finite continuous-to-ordinary cohomology comparison.  This supplies the
inverse law independently of the still-missing cyclic tensor-product addition formula.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Negating a base-unit cyclic `H²` parameter gives the Brauer inverse. -/
theorem cyclicGaloisH2Parameter_brauerTensorNeg
    (a : Additive Kˣ) :
    brauerTensorNeg K (brauerClass (cyclicGaloisH2ParameterCSA K L a)) =
      brauerClass (cyclicGaloisH2ParameterCSA K L (-a)) := by
  change brauerTensorNeg K
    (brauerClass (cyclicGaloisAlgebraCSA K L (a.toMul : K) a.toMul.ne_zero)) =
      brauerClass (cyclicGaloisAlgebraCSA K L ((-a).toMul : K) (-a).toMul.ne_zero)
  simpa only [toMul_neg, Units.val_inv_eq_inv_val] using
    cyclicGaloisAlgebra_brauerTensorNeg K L (a.toMul : K) a.toMul.ne_zero

/-- The selected cyclic degree-two cohomology representative sends cohomological negation to
Brauer inversion in every finite cyclic degree. -/
theorem cyclicGaloisH2BrauerMap_brauerTensorNeg
    (z : cyclicGaloisH2 K L) :
    brauerTensorNeg K (cyclicGaloisH2BrauerMap K L z) = cyclicGaloisH2BrauerMap K L (-z) := by
  obtain ⟨a, ha⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  calc
    brauerTensorNeg K (cyclicGaloisH2BrauerMap K L z) =
        brauerTensorNeg K (brauerClass (cyclicGaloisH2ParameterCSA K L a)) := by
      rw [cyclicGaloisH2Parameter_brauerClass_eq_brauerMap_of_baseProjection K L a z ha]
    _ = brauerClass (cyclicGaloisH2ParameterCSA K L (-a)) :=
      cyclicGaloisH2Parameter_brauerTensorNeg K L a
    _ = cyclicGaloisH2BrauerMap K L (-z) := by
      apply cyclicGaloisH2Parameter_brauerClass_eq_brauerMap_of_baseProjection K L (-a) (-z)
      rw [map_neg, ha]

/-- The finite continuous cyclic `H²` bridge carries cohomological negation to Brauer
inversion. -/
theorem finiteGaloisContinuousCyclicH2BrauerMap_brauerTensorNeg
    (z : continuousGaloisUnitCohomology 2 K L) :
    brauerTensorNeg K (finiteGaloisContinuousCyclicH2BrauerMap K L z) =
      finiteGaloisContinuousCyclicH2BrauerMap K L (-z) := by
  change brauerTensorNeg K
      (cyclicGaloisH2BrauerMap K L (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)) =
    cyclicGaloisH2BrauerMap K L
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L (-z))
  rw [map_neg]
  exact cyclicGaloisH2BrauerMap_brauerTensorNeg K L
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)

/-- In a finite cyclic coordinate system, parameter negation gives the Brauer inverse for the
selected continuous `H²` representative. -/
theorem finiteGaloisContinuousCyclicH2InvariantBrauerMap_brauerTensorNeg
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ZMod n) (z : ZMod n) :
    brauerTensorNeg K (finiteGaloisContinuousCyclicH2InvariantBrauerMap K L n e z) =
      finiteGaloisContinuousCyclicH2InvariantBrauerMap K L n e (-z) := by
  change brauerTensorNeg K (finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm z)) =
    finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm (-z))
  rw [map_neg]
  exact finiteGaloisContinuousCyclicH2BrauerMap_brauerTensorNeg K L (e.symm z)

end GaloisForLFunctions.HTGeometry.ABHN
