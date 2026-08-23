import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisH2BrauerAdditive
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionTensorProduct

/-!
# Local additive quadratic cyclic Brauer factors

Composing the additive degree-two cyclic `H²`-to-Brauer map with scalar extension gives an
additive factor at every field extension, hence at every global completion.  This is the local
additivity prerequisite for comparing such factors with future ABHN invariant maps.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable {K E L : Type} [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- The additive quadratic cyclic `H²` Brauer factor after scalar extension to `E`. -/
noncomputable def quadraticCyclicGaloisH2ScalarExtensionBrauerAddHom
    (hdeg : Module.finrank K L = 2)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2) :
    cyclicGaloisH2 K L →+ BrauerGroup E :=
  (scalarExtensionBrauerAddHom K E).comp
    (quadraticCyclicGaloisH2BrauerAddHom K L hdeg e)

/-- The selected local quadratic cyclic `H²` class agrees with the additive local factor. -/
theorem scalarExtension_quadraticCyclicGaloisH2BrauerMap_eq_addHom
    (hdeg : Module.finrank K L = 2)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2)
    (z : cyclicGaloisH2 K L) :
    scalarExtensionBrauerMap K E (quadraticCyclicGaloisH2BrauerMap K L hdeg z) =
      quadraticCyclicGaloisH2ScalarExtensionBrauerAddHom hdeg e z := by
  rw [quadraticCyclicGaloisH2BrauerMap_eq_addHom]
  rfl

/-- Local quadratic cyclic `H²` Brauer factors preserve addition at every scalar extension. -/
theorem scalarExtension_quadraticCyclicGaloisH2BrauerMap_add
    (hdeg : Module.finrank K L = 2)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2)
    (x y : cyclicGaloisH2 K L) :
    scalarExtensionBrauerMap K E (quadraticCyclicGaloisH2BrauerMap K L hdeg (x + y)) =
      scalarExtensionBrauerMap K E (quadraticCyclicGaloisH2BrauerMap K L hdeg x) +
        scalarExtensionBrauerMap K E (quadraticCyclicGaloisH2BrauerMap K L hdeg y) := by
  rw [scalarExtension_quadraticCyclicGaloisH2BrauerMap_eq_addHom,
    scalarExtension_quadraticCyclicGaloisH2BrauerMap_eq_addHom,
    scalarExtension_quadraticCyclicGaloisH2BrauerMap_eq_addHom]
  exact (quadraticCyclicGaloisH2ScalarExtensionBrauerAddHom hdeg e).map_add x y

end GaloisForLFunctions.HTGeometry.ABHN
