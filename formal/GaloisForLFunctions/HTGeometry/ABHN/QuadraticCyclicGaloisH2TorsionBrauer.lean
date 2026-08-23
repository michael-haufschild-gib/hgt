import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisAlgebraOpposite
import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisH2Brauer
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousQuadraticGaloisH2Brauer

/-!
# Two-torsion of quadratic cyclic cohomological Brauer representatives

The explicit opposite equivalence of a quadratic cyclic algebra proves that its Brauer class is
two-torsion.  This module transfers that closed structural result to both existing quadratic
cyclic `H²` representative functions.  It proves an image constraint, not additivity of those
functions; the latter still requires the full cyclic tensor-product formula.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
  [FiniteDimensional K L] [IsGalois K L]

/-- Every quadratic cyclic unit parameter defines a Brauer class killed by two. -/
theorem two_zsmul_quadraticCyclicGaloisH2ParameterCSA_brauerClass_eq_zero
    (hdeg : Module.finrank K L = 2) (a : Additive Kˣ) :
    (2 : ℤ) • brauerClass (quadraticCyclicGaloisH2ParameterCSA K L hdeg a) = 0 := by
  change (2 : ℤ) • brauerClass
    (quadraticCyclicGaloisAlgebraCSA K L hdeg (a.toMul : K) a.toMul.ne_zero) = 0
  exact two_zsmul_quadraticCyclicGaloisAlgebra_brauerClass_eq_zero K L hdeg _ _

/-- Every selected quadratic cyclic ordinary `H²` Brauer representative is killed by two. -/
theorem two_zsmul_quadraticCyclicGaloisH2BrauerMap_eq_zero
    (hdeg : Module.finrank K L = 2) (z : cyclicGaloisH2 K L) :
    (2 : ℤ) • quadraticCyclicGaloisH2BrauerMap K L hdeg z = 0 := by
  change (2 : ℤ) • brauerClass (quadraticCyclicGaloisH2ParameterCSA K L hdeg
    (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
      (cyclicGaloisH2Representative K L z)))) = 0
  exact two_zsmul_quadraticCyclicGaloisH2ParameterCSA_brauerClass_eq_zero K L hdeg _

/-- Every selected finite continuous quadratic cyclic `H²` Brauer representative is killed by
two. -/
theorem two_zsmul_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_zero
    (hdeg : Module.finrank K L = 2) (z : continuousGaloisUnitCohomology 2 K L) :
    (2 : ℤ) • finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg z = 0 := by
  change (2 : ℤ) • quadraticCyclicGaloisH2BrauerMap K L hdeg
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) = 0
  exact two_zsmul_quadraticCyclicGaloisH2BrauerMap_eq_zero K L hdeg _

end GaloisForLFunctions.HTGeometry.ABHN
