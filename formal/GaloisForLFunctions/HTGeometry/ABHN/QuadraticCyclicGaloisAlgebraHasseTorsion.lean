import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisH2TorsionBrauer
import GaloisForLFunctions.HTGeometry.ABHN.HasseCentralSimple
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionTensorProduct

/-!
# Local two-torsion of quadratic cyclic Brauer classes

Scalar extension is additive on Brauer groups.  Thus the explicit exponent-two law for
quadratic cyclic algebras persists at every completion of a number field or global function
field.  These are local constraints on the Brauer targets which a future local invariant map
must preserve.

They do not supply the local invariant isomorphism or ABHN reciprocity: they isolate the
quadratic, two-primary piece already forced by cyclic algebra structure.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

variable {K E L : Type} [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Scalar extension preserves the exponent-two law for a nonzero quadratic cyclic algebra. -/
theorem scalarExtension_two_zsmul_quadraticCyclicGaloisAlgebra_brauerClass_eq_zero
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    (2 : ℤ) • scalarExtensionBrauerMap K E
      (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) = 0 := by
  change (2 : ℤ) • scalarExtensionBrauerAddHom K E
    (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) = 0
  rw [← (scalarExtensionBrauerAddHom K E).map_zsmul]
  rw [two_zsmul_quadraticCyclicGaloisAlgebra_brauerClass_eq_zero, map_zero]

/-- Scalar extension preserves the exponent-two law for each selected quadratic cyclic ordinary
`H²` Brauer representative. -/
theorem scalarExtension_two_zsmul_quadraticCyclicGaloisH2BrauerMap_eq_zero
    (hdeg : Module.finrank K L = 2) (z : cyclicGaloisH2 K L) :
    (2 : ℤ) • scalarExtensionBrauerMap K E
      (quadraticCyclicGaloisH2BrauerMap K L hdeg z) = 0 := by
  change (2 : ℤ) • scalarExtensionBrauerAddHom K E
    (quadraticCyclicGaloisH2BrauerMap K L hdeg z) = 0
  rw [← (scalarExtensionBrauerAddHom K E).map_zsmul]
  rw [two_zsmul_quadraticCyclicGaloisH2BrauerMap_eq_zero, map_zero]

/-- Scalar extension preserves the exponent-two law for each selected finite continuous
quadratic cyclic `H²` Brauer representative. -/
theorem scalarExtension_two_zsmul_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_zero
    (hdeg : Module.finrank K L = 2) (z : continuousGaloisUnitCohomology 2 K L) :
    (2 : ℤ) • scalarExtensionBrauerMap K E
      (finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg z) = 0 := by
  change (2 : ℤ) • scalarExtensionBrauerAddHom K E
    (finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg z) = 0
  rw [← (scalarExtensionBrauerAddHom K E).map_zsmul]
  rw [two_zsmul_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_zero, map_zero]

/-- Every completion of a number field sees the quadratic cyclic Brauer class as two-torsion. -/
theorem numberFieldLocal_two_zsmul_quadraticCyclicGaloisAlgebra_brauerClass_eq_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K) :
    (2 : ℤ) • brauerClass (scalarExtensionCSA (L := completion K p)
      (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) = 0 := by
  change (2 : ℤ) • scalarExtensionBrauerMap K (completion K p)
    (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) = 0
  exact scalarExtension_two_zsmul_quadraticCyclicGaloisAlgebra_brauerClass_eq_zero hdeg a ha

/-- The quadratic cyclic ordinary `H²` representative is two-torsion at every number-field
completion. -/
theorem numberFieldLocal_two_zsmul_quadraticCyclicGaloisH2BrauerMap_eq_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (z : cyclicGaloisH2 K L) (p : NumberFieldPlace K) :
    (2 : ℤ) • scalarExtensionBrauerMap K (completion K p)
      (quadraticCyclicGaloisH2BrauerMap K L hdeg z) = 0 := by
  exact scalarExtension_two_zsmul_quadraticCyclicGaloisH2BrauerMap_eq_zero hdeg z

/-- Every completion of a global function field sees the quadratic cyclic Brauer class as
two-torsion. -/
theorem rationalFunctionLocal_two_zsmul_quadraticCyclicGaloisAlgebra_brauerClass_eq_zero
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L/RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (hdeg : Module.finrank (RatFunc F) L = 2) (a : RatFunc F) (ha : a ≠ 0)
    (p : RationalFunctionPlace F) :
    (2 : ℤ) • brauerClass (scalarExtensionCSA (L := rationalFunctionCompletion F p)
      (quadraticCyclicGaloisAlgebraCSA (RatFunc F) L hdeg a ha)) = 0 := by
  change (2 : ℤ) • scalarExtensionBrauerMap (RatFunc F) (rationalFunctionCompletion F p)
    (brauerClass (quadraticCyclicGaloisAlgebraCSA (RatFunc F) L hdeg a ha)) = 0
  exact scalarExtension_two_zsmul_quadraticCyclicGaloisAlgebra_brauerClass_eq_zero hdeg a ha

/-- The quadratic cyclic ordinary `H²` representative is two-torsion at every global
function-field completion. -/
theorem rationalFunctionLocal_two_zsmul_quadraticCyclicGaloisH2BrauerMap_eq_zero
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L/RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (hdeg : Module.finrank (RatFunc F) L = 2) (z : cyclicGaloisH2 (RatFunc F) L)
    (p : RationalFunctionPlace F) :
    (2 : ℤ) • scalarExtensionBrauerMap (RatFunc F) (rationalFunctionCompletion F p)
      (quadraticCyclicGaloisH2BrauerMap (RatFunc F) L hdeg z) = 0 := by
  exact scalarExtension_two_zsmul_quadraticCyclicGaloisH2BrauerMap_eq_zero hdeg z

end GaloisForLFunctions.HTGeometry.ABHN
