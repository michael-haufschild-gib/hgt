import GaloisForLFunctions.HTGeometry.MeromorphicDomainReflection
import GaloisForLFunctions.HTGeometry.QuadraticSemilinearInvolution
import GaloisForLFunctions.RHTower.XiCriticalStripMarkedComponent
import GaloisForLFunctions.RHTower.XiReflectedFactorSeparation

noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry
open scoped IntermediateField

theorem strip_reflection_preserves_domain (z : ℂ) (hz : z ∈ stripDomain.carrier) :
    1 - z ∈ stripDomain.carrier := by
  change 0 < (1 - z).re ∧ (1 - z).re < 1
  change 0 < z.re ∧ z.re < 1 at hz
  simp only [Complex.sub_re, Complex.one_re]
  constructor <;> linarith [hz.1, hz.2]

def stripReflection : StripField ≃+* StripField :=
  stripDomain.reflectEquiv 1 strip_reflection_preserves_domain

theorem stripReflection_involutive : Function.Involutive stripReflection :=
  stripDomain.reflectEquiv_involutive 1 strip_reflection_preserves_domain

theorem stripReflection_base (a : K) :
    stripReflection (algebraMap K StripField a) =
      algebraMap K StripField (planeReflectEquiv 1 a) :=
  stripDomain.reflectEquiv_restrictPlane 1 strip_reflection_preserves_domain a

theorem stripReflection_xi :
    stripReflection (algebraMap K StripField xiElement) =
      algebraMap K StripField xiElement := by
  rw [stripReflection_base, planeReflectEquiv_xiElement]

theorem strip_reflected_factor_isSquare {n : ℕ} (hn : 1 ≤ n) :
    IsSquare (algebraMap K StripField (reflectedElement n)) := by
  have h := (strip_factor_isSquare hn).map stripReflection.toRingHom
  change IsSquare (stripReflection (algebraMap K StripField (factorElement n))) at h
  rwa [stripReflection_base] at h

/-- Functional reflection lifts involutively to the actual common quadratic strip component. -/
def stripQuadraticReflection : stripQuadraticField ≃+* stripQuadraticField :=
  quadraticSemilinearEquiv stripXiRoot_sq strip_xi_not_isSquare stripReflection stripReflection_xi

theorem stripQuadraticReflection_base (a : StripField) :
    stripQuadraticReflection (algebraMap StripField stripQuadraticField a) =
      algebraMap StripField stripQuadraticField (stripReflection a) :=
  quadraticSemilinearEquiv_base stripXiRoot_sq strip_xi_not_isSquare
    stripReflection stripReflection_xi a

theorem stripQuadraticReflection_global_base (a : K) :
    stripQuadraticReflection (algebraMap K stripQuadraticField a) =
      algebraMap K stripQuadraticField (planeReflectEquiv 1 a) := by
  rw [IsScalarTower.algebraMap_apply K StripField stripQuadraticField,
    stripQuadraticReflection_base, stripReflection_base,
    IsScalarTower.algebraMap_apply K StripField stripQuadraticField]

theorem stripQuadraticReflection_gen :
    stripQuadraticReflection (IntermediateField.AdjoinSimple.gen StripField stripXiRoot) =
      IntermediateField.AdjoinSimple.gen StripField stripXiRoot :=
  quadraticSemilinearEquiv_gen stripXiRoot_sq strip_xi_not_isSquare
    stripReflection stripReflection_xi

theorem stripQuadraticReflection_involutive : Function.Involutive stripQuadraticReflection :=
  quadraticSemilinearEquiv_involutive stripXiRoot_sq strip_xi_not_isSquare
    stripReflection stripReflection_xi stripReflection_involutive

end RHTower.XiGlobalKummer
