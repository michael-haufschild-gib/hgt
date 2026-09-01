import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedFieldDomain
import GaloisForLFunctions.HTGeometry.MeromorphicPeriodicScalarExtension
import GaloisForLFunctions.HTGeometry.BesselOrderDifferentialClosureObstruction
import GaloisForLFunctions.HTGeometry.DifferentialFieldSolution

/-!
# Common differential closure of Bessel and periodic constants

The Bessel parameterized Galois development uses `Constants`, the differential closure of `ℂ`.
The actual global meromorphic realization has the much larger field of unit-periodic meromorphic
functions as its difference constants.  Their tensor product over the algebraically closed field
`ℂ` is a domain.  Its fraction field and differential closure therefore give one concrete
differentially closed field containing faithful copies of both constant fields.
-/

open scoped Differential TensorProduct UnivMeroFieldInstances
open Filter Set Topology Function Complex

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

local instance besselPeriodicCompositumComplexDifferential : Differential ℂ :=
  complexZeroDifferential

local instance besselPeriodicCompositumPeriodicDifferential :
    Differential UnitPeriodicMeromorphicField :=
  derivationClosedDifferential _
    (GaloisForLFunctions.meromorphicTranslationFixedField_derivationClosed 1)

local instance besselPeriodicCompositumConstantsDifferentialAlgebra :
    DifferentialAlgebra ℂ Constants :=
  DiffFieldExt.differentialAlgebra (diffClosureExt (F := ℂ))

local instance besselPeriodicCompositumPeriodicDifferentialAlgebra :
    DifferentialAlgebra ℂ UnitPeriodicMeromorphicField := by
  constructor
  intro c
  apply Subtype.ext
  change Differential.deriv (algebraMap ℂ (meroField Set.univ) c) =
    algebraMap ℂ (meroField Set.univ) (Differential.deriv c)
  rw [show Differential.deriv c = 0 by rfl, map_zero]
  change
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ c))′ = 0
  rw [meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ
    Set.univ_nonempty]
  have hconst : analyticSubringDeriv isOpen_univ
      (constToAnalytic Set.univ c) = 0 := by
    apply Subtype.ext
    rw [analyticSubringDeriv_coe]
    let f : ℂ → ℂ := fun _ => c
    calc
      Germ.coeRingHom (Filter.principal Set.univ) (deriv f) =
          Germ.coeRingHom (Filter.principal Set.univ) (0 : ℂ → ℂ) := by
        congr 1
        funext z
        simp [f]
      _ = 0 := (Germ.coeRingHom (Filter.principal Set.univ)).map_zero
  rw [hconst, map_zero]

/-- Domain joining the original differential constants and actual unit-periodic constants. -/
abbrev BesselPeriodicConstantTensor :=
  Constants ⊗[ℂ] UnitPeriodicMeromorphicField

noncomputable instance besselPeriodicCompositumTensorIsDomain :
    IsDomain BesselPeriodicConstantTensor :=
  isDomain_tensorProduct_of_fields

noncomputable instance besselPeriodicCompositumTensorDifferential :
    Differential BesselPeriodicConstantTensor :=
  tensorProductDifferential

noncomputable instance besselPeriodicCompositumTensorRatAlgebra :
    Algebra ℚ BesselPeriodicConstantTensor :=
  ((algebraMap ℂ BesselPeriodicConstantTensor).comp (algebraMap ℚ ℂ)).toAlgebra

/-- Fraction field of the joined constant domain. -/
abbrev BesselPeriodicConstantField := FractionRing BesselPeriodicConstantTensor

noncomputable instance besselPeriodicCompositumFieldComplexAlgebra :
    Algebra ℂ BesselPeriodicConstantField :=
  ((algebraMap BesselPeriodicConstantTensor BesselPeriodicConstantField).comp
    (algebraMap ℂ BesselPeriodicConstantTensor)).toAlgebra

noncomputable instance besselPeriodicCompositumFieldRatAlgebra :
    Algebra ℚ BesselPeriodicConstantField :=
  ((algebraMap BesselPeriodicConstantTensor BesselPeriodicConstantField).comp
    (algebraMap ℚ BesselPeriodicConstantTensor)).toAlgebra

noncomputable instance besselPeriodicCompositumFieldDifferential :
    Differential BesselPeriodicConstantField :=
  fractionRingDifferential BesselPeriodicConstantTensor

/-- Differentially closed common constant field used for the actual Bessel realization. -/
abbrev BesselPeriodicConstants := diffClosure BesselPeriodicConstantField

noncomputable instance besselPeriodicCompositumConstantsComplexAlgebra :
    Algebra ℂ BesselPeriodicConstants :=
  ((algebraMap BesselPeriodicConstantField BesselPeriodicConstants).comp
    (algebraMap ℂ BesselPeriodicConstantField)).toAlgebra

/-- Faithful copy of the original Bessel differential constants in the common closure. -/
def constantsToBesselPeriodicConstants : Constants →ₐ[ℂ] BesselPeriodicConstants :=
  { toRingHom :=
      ((algebraMap BesselPeriodicConstantField BesselPeriodicConstants).comp
        (algebraMap BesselPeriodicConstantTensor BesselPeriodicConstantField)).comp
          (Algebra.TensorProduct.includeLeft :
            Constants →ₐ[ℂ] BesselPeriodicConstantTensor).toRingHom
    commutes' := fun _ => rfl }

/-- Faithful copy of actual unit-periodic meromorphic constants in the common closure. -/
def periodicToBesselPeriodicConstants :
    UnitPeriodicMeromorphicField →ₐ[ℂ] BesselPeriodicConstants :=
  { toRingHom :=
      ((algebraMap BesselPeriodicConstantField BesselPeriodicConstants).comp
        (algebraMap BesselPeriodicConstantTensor BesselPeriodicConstantField)).comp
          (Algebra.TensorProduct.includeRight :
            UnitPeriodicMeromorphicField →ₐ[ℂ] BesselPeriodicConstantTensor).toRingHom
    commutes' := fun c => by
      have hbalance :
          (1 : Constants) ⊗ₜ[ℂ]
              algebraMap ℂ UnitPeriodicMeromorphicField c =
            algebraMap ℂ Constants c ⊗ₜ[ℂ]
              (1 : UnitPeriodicMeromorphicField) := by
        simpa only [Algebra.smul_def, mul_one] using
          (TensorProduct.smul_tmul (R := ℂ) c
            (1 : Constants) (1 : UnitPeriodicMeromorphicField)).symm
      change (algebraMap BesselPeriodicConstantField BesselPeriodicConstants)
          ((algebraMap BesselPeriodicConstantTensor BesselPeriodicConstantField)
            ((1 : Constants) ⊗ₜ[ℂ]
              algebraMap ℂ UnitPeriodicMeromorphicField c)) =
        (algebraMap BesselPeriodicConstantField BesselPeriodicConstants)
          ((algebraMap BesselPeriodicConstantTensor BesselPeriodicConstantField)
            (algebraMap ℂ Constants c ⊗ₜ[ℂ]
              (1 : UnitPeriodicMeromorphicField)))
      rw [hbalance] }

end


end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
