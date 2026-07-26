import GaloisForLFunctions.HTGeometry.MeromorphicRatFuncTranslation
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit

/-!
# The global meromorphic instance stack

Modules working with meromorphic functions on all of `ℂ` need the same instances: the analytic
subring is a domain and a `ℂ`-algebra, the meromorphic field is a characteristic zero algebra over
both `ℂ` and `RatFunc ℂ`, and both it and `RatFunc ℂ` carry their canonical derivations,
compatibly.

`Set.univ` is open, preconnected, nonempty and infinite, so every side condition is discharged once
here rather than at each use.  These are data-carrying classes, so they are *scoped*: a module opts
in with `open scoped UnivMeroFieldInstances` and modules that do not opt in see no change to
instance resolution.
-/

open Set Complex
open scoped Differential
open Bottcher
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace UnivMeroFieldInstances

noncomputable section

scoped instance univAnalyticDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

scoped instance univComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

scoped instance univComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

scoped instance univMeroDifferential :
    Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

scoped instance univRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

scoped instance univRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

scoped instance univRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

scoped instance univMeroCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

end

end UnivMeroFieldInstances
