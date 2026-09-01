import GaloisForLFunctions.HTGeometry.DifferenceFieldScalarExtensionSimple
import GaloisForLFunctions.HTGeometry.DifferentialClosureClosed
import GaloisForLFunctions.HTGeometry.MeromorphicEllipticCompositum
import GaloisForLFunctions.HTGeometry.TensorProductDifferential
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAdjoin
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Periodic-constant scalar extension of the global meromorphic field

The fixed field of unit translation on global meromorphic germs is a differential field.  Extend
it to its differential closure and tensor back with the meromorphic field.  The resulting
difference-differential ring is sigma-simple, has exactly the differential closure as its fixed
field, and its shift commutes with the tensor derivation.

This is the concrete meromorphic scalar ring in Dreyfus's parameterized Picard--Vessiot
construction; all Hilbert, differentiability, and constant-field structure is discharged here.
-/

open scoped Differential TensorProduct UnivMeroFieldInstances

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- Field of global meromorphic germs fixed by unit translation. -/
abbrev UnitPeriodicMeromorphicField :=
  GaloisForLFunctions.meromorphicTranslationFixedField (1 : ℂ)

local instance unitPeriodicDifferential : Differential UnitPeriodicMeromorphicField :=
  derivationClosedDifferential _
    (GaloisForLFunctions.meromorphicTranslationFixedField_derivationClosed 1)

local instance unitPeriodicMeroDifferentialAlgebra :
    DifferentialAlgebra UnitPeriodicMeromorphicField (meroField Set.univ) :=
  derivationClosed_differentialAlgebra _
    (GaloisForLFunctions.meromorphicTranslationFixedField_derivationClosed 1)

local instance periodicDiffClosureDifferentialAlgebra :
    DifferentialAlgebra UnitPeriodicMeromorphicField
      (diffClosure UnitPeriodicMeromorphicField) :=
  DiffFieldExt.differentialAlgebra (diffClosureExt (F := UnitPeriodicMeromorphicField))

/-- Differentially closed periodic-constant scalar extension of global meromorphic germs. -/
abbrev MeromorphicPeriodicScalarExtension :=
  diffClosure UnitPeriodicMeromorphicField ⊗[UnitPeriodicMeromorphicField]
    meroField Set.univ

local instance meromorphicPeriodicScalarDifferential :
    Differential MeromorphicPeriodicScalarExtension :=
  tensorProductDifferential

local instance meromorphicPeriodicScalarDifferentialAlgebra :
    DifferentialAlgebra (diffClosure UnitPeriodicMeromorphicField)
      MeromorphicPeriodicScalarExtension :=
  tensorProductDifferentialAlgebra_left

theorem unitTranslation_fixed_periodic (c : UnitPeriodicMeromorphicField) :
    addTranslationMeroEquiv 1
        (algebraMap UnitPeriodicMeromorphicField (meroField Set.univ) c) =
      algebraMap UnitPeriodicMeromorphicField (meroField Set.univ) c := by
  exact c.property

theorem unitTranslation_exact_periodic
    (x : meroField Set.univ) (hx : addTranslationMeroEquiv 1 x = x) :
    ∃ c : UnitPeriodicMeromorphicField,
      x = algebraMap UnitPeriodicMeromorphicField (meroField Set.univ) c := by
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Unit translation acting trivially on the differentially closed periodic constants. -/
def meromorphicPeriodicScalarShift :
    MeromorphicPeriodicScalarExtension ≃+* MeromorphicPeriodicScalarExtension :=
  scalarExtensionSigma (C := UnitPeriodicMeromorphicField)
    (L := diffClosure UnitPeriodicMeromorphicField)
    (F := meroField Set.univ)
    (addTranslationMeroEquiv 1) unitTranslation_fixed_periodic

/-- Dreyfus scalar-extension lemma specialized to global meromorphic germs. -/
theorem meromorphicPeriodicScalarShift_isSigmaSimple :
    IsSigmaSimple meromorphicPeriodicScalarShift :=
  scalarExtension_isSigmaSimple
    (C := UnitPeriodicMeromorphicField)
    (L := diffClosure UnitPeriodicMeromorphicField)
    (F := meroField Set.univ)
    (addTranslationMeroEquiv 1) unitTranslation_fixed_periodic
    unitTranslation_exact_periodic

/-- Fixed elements of the scalar extension are precisely its left periodic-constant factor. -/
theorem meromorphicPeriodicScalarShift_fixed
    {z : MeromorphicPeriodicScalarExtension}
    (hz : meromorphicPeriodicScalarShift z = z) :
    ∃ c : diffClosure UnitPeriodicMeromorphicField,
      z = Algebra.TensorProduct.includeLeft
        (R := UnitPeriodicMeromorphicField)
        (S := UnitPeriodicMeromorphicField)
        (A := diffClosure UnitPeriodicMeromorphicField)
        (B := meroField Set.univ) c := by
  exact scalarExtension_fixed_eq_includeLeft
    (C := UnitPeriodicMeromorphicField)
    (L := diffClosure UnitPeriodicMeromorphicField)
    (F := meroField Set.univ)
    (addTranslationMeroEquiv 1) unitTranslation_fixed_periodic
    unitTranslation_exact_periodic hz

/-- Unit translation commutes with the tensor-product derivation. -/
theorem meromorphicPeriodicScalarShift_deriv
    (x : MeromorphicPeriodicScalarExtension) :
    meromorphicPeriodicScalarShift (Differential.deriv x) =
      Differential.deriv (meromorphicPeriodicScalarShift x) := by
  simpa [meromorphicPeriodicScalarShift, scalarExtensionSigma] using
    (asymmetricDifferenceTensorEquiv_deriv
      (K := UnitPeriodicMeromorphicField)
      (A := diffClosure UnitPeriodicMeromorphicField)
      (B := meroField Set.univ)
      (RingEquiv.refl UnitPeriodicMeromorphicField)
      (RingEquiv.refl (diffClosure UnitPeriodicMeromorphicField))
      (addTranslationMeroEquiv 1)
      (fun _ => rfl) unitTranslation_fixed_periodic
      (fun _ => rfl) (addTranslationMeroEquiv_deriv 1) x)

end

end GaloisForLFunctions.HTGeometry
