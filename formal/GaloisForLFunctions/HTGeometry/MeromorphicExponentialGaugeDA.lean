import GaloisForLFunctions.HTGeometry.MeromorphicPhysicalCharacteristicIncidence
import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit
import GaloisForLFunctions.HTGeometry.AffineFirstOrderDifferentialAlgebraicity

/-!
# Differential algebraicity of genuine meromorphic exponential gauges

An element satisfying the static first-order constraint `y' = a*y`, with `a` in the base
field, is differentially algebraic.  Applying this finite-jet fact to the genuine global
meromorphic exponential constructed by `physicalExponentialMero` proves that every elementary
exponential clock gauge is differentially algebraic over `C(z)`.

This closes the gauge hypothesis used by exact Gamma-valued physics observables.  Multiplication
by `exp(lambda*z)` therefore changes neither their differential-algebraic nor their
hypertranscendental regime.  The theorem is about the observable's differential constraint, not
about solving or propagating an evolution equation.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

namespace HTGeometry

end HTGeometry

local instance meromorphicExponentialGaugeDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicExponentialGaugeComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance meromorphicExponentialGaugeComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance meromorphicExponentialGaugeDifferential :
    Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance meromorphicExponentialGaugeRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance meromorphicExponentialGaugeRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance meromorphicExponentialGaugeDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

/-- The analytic representative of the physical exponential satisfies its expected first-order
differential constraint inside the analytic-germ domain. -/
theorem analyticSubringDeriv_physicalExponentialAnalytic (lambda : ℂ) :
    analyticSubringDeriv isOpen_univ (physicalExponentialAnalytic lambda) =
      constToAnalytic Set.univ lambda * physicalExponentialAnalytic lambda := by
  apply Subtype.ext
  change
    Germ.ofFun (l := Filter.principal Set.univ)
        (deriv (fun z : ℂ => Complex.exp (lambda * z))) =
      Germ.ofFun (l := Filter.principal Set.univ)
        (fun z : ℂ => lambda * Complex.exp (lambda * z))
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    simpa [mul_comm] using! ((Complex.hasDerivAt_exp (lambda * z)).comp z
      ((hasDerivAt_const z lambda).mul (hasDerivAt_id z))).deriv

/-- The genuine global meromorphic exponential is an eigenvector of differentiation. -/
theorem physicalExponentialMero_deriv (lambda : ℂ) :
    (physicalExponentialMero lambda)′ =
      algebraMap ℂ (meroField Set.univ) lambda *
        physicalExponentialMero lambda := by
  rw [physicalExponentialMero,
    meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ
      Set.univ_nonempty,
    analyticSubringDeriv_physicalExponentialAnalytic, map_mul]
  rfl

/-- Every genuine meromorphic exponential gauge is differentially algebraic over `C(z)`. -/
theorem differentialAlgebraicOver_physicalExponentialMero (lambda : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (physicalExponentialMero lambda) := by
  have hC : algebraMap (RatFunc ℂ) (meroField Set.univ) (RatFunc.C lambda) =
      algebraMap ℂ (meroField Set.univ) lambda := by
    change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (RatFunc.C lambda) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ lambda)
    rw [show RatFunc.C lambda =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C lambda) by rfl,
      ratfuncToMero_algebraMap_polynomial]
    change algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (polyToAnalytic Set.univ (Polynomial.C lambda)) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ lambda)
    congr 1
    apply Subtype.ext
    change Germ.ofFun (l := Filter.principal Set.univ)
        (fun z : ℂ => (Polynomial.C lambda).eval z) =
      Germ.ofFun (l := Filter.principal Set.univ) (fun _ : ℂ => lambda)
    rw [Germ.coe_eq]
    exact eventually_principal.mpr fun z _ => by simp
  apply HTGeometry.differentialAlgebraicOver_of_deriv_eq_base_mul
    (RatFunc.C lambda)
  rw [physicalExponentialMero_deriv, hC]

end

end GaloisForLFunctions
