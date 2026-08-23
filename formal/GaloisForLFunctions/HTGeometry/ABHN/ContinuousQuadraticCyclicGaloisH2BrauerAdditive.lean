import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisH2BrauerAdditive

/-!
# Additivity of continuous quadratic cyclic cohomological Brauer maps

The finite continuous-to-ordinary cohomology comparison transports the closed additive
quadratic cyclic `H²`-to-Brauer bridge to finite continuous Galois cohomology.  This is a finite
local-class-field-theory interface: it remains conditional only on the supplied `ℤ/2ℤ`
presentation of the norm quotient, not on any unproved mathematical assumption.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
  [FiniteDimensional K L] [IsGalois K L]

/-- The finite continuous-to-ordinary degree-two comparison as an additive homomorphism. -/
noncomputable def finiteGaloisContinuousH2ToOrdinaryH2AddHom :
    continuousGaloisUnitCohomology 2 K L →+ cyclicGaloisH2 K L where
  toFun := finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L
  map_zero' := by
    exact map_zero (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L)
  map_add' := by
    intro x y
    exact map_add (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L) x y

/-- The additive refinement of the selected finite continuous quadratic cyclic `H²` Brauer map. -/
noncomputable def finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerAddHom
    (hdeg : Module.finrank K L = 2)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2) :
    continuousGaloisUnitCohomology 2 K L →+ BrauerGroup K :=
  (quadraticCyclicGaloisH2BrauerAddHom K L hdeg e).comp
    (finiteGaloisContinuousH2ToOrdinaryH2AddHom K L)

/-- The original finite continuous quadratic cyclic Brauer representative agrees pointwise with
its additive refinement. -/
theorem finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_addHom
    (hdeg : Module.finrank K L = 2)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2)
    (z : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg z =
      finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerAddHom K L hdeg e z := by
  change quadraticCyclicGaloisH2BrauerMap K L hdeg
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) = _
  rw [quadraticCyclicGaloisH2BrauerMap_eq_addHom]
  rfl

/-- The finite continuous quadratic cyclic Brauer map preserves addition under the supplied
quadratic norm-quotient presentation. -/
theorem finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_add
    (hdeg : Module.finrank K L = 2)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2)
    (x y : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg (x + y) =
      finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg x +
        finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg y := by
  rw [finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_addHom,
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_addHom,
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_addHom]
  exact (finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerAddHom K L hdeg e).map_add x y

/-- The finite continuous quadratic cyclic Brauer map sends zero to zero in additive Brauer
notation. -/
theorem finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_zero
    (hdeg : Module.finrank K L = 2)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2) :
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg 0 = 0 := by
  rw [finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_addHom]
  exact (finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerAddHom K L hdeg e).map_zero

end GaloisForLFunctions.HTGeometry.ABHN
