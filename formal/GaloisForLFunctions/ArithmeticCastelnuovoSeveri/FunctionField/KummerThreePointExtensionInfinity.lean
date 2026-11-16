import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityCoordinate
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The reciprocal chart after extending constants

Coordinate inversion identifies the fixed-degree three-point field
with its reciprocal presentation. Its actual polynomial normalization
is a finite free Dedekind domain over the extended constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
    (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
    (c : Eˣ) (a : ℕ)
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "F" => FractionRing E[X]

/-- The original three-point field expressed in the reciprocal coordinate. -/
abbrev PrimePowerThreePointExtensionInfinityField := KummerInfinityField c 0 a (M - 1)
local notation "L" => PrimePowerThreePointExtensionInfinityField p d n E c a

omit [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] in
/-- The reciprocal presentation preserves the original cyclic degree. -/
theorem primePowerThreePointExtensionInfinity_finrank : Module.finrank F L = M := by
  rw [kummerInfinityField_finrank, primePowerThreePointExtension_index]

/-- Coordinate inversion preserves the actual Galois extension. -/
theorem primePowerThreePointExtensionInfinity_isGalois : IsGalois F L := by
  letI := primePowerThreePointExtension_isGalois p d n E c a
  apply IsGalois.of_equiv_equiv
    (f := (kummerCoordinateInversion E).toRingEquiv)
    (g := (kummerInfinityFieldEquiv c 0 a (M - 1)).toRingEquiv)
  ext x
  exact (kummerInfinityFieldEquiv_algebraMap c 0 a (M - 1) x).symm

/-- The integral closure of the reciprocal polynomial base in the actual function field. -/
abbrev PrimePowerThreePointExtensionInfinityNormalization := integralClosure E[X] L
local notation "B" => PrimePowerThreePointExtensionInfinityNormalization p d n E c a

/-- Separability makes the reciprocal normalization Dedekind. -/
instance primePowerThreePointExtensionInfinityNormalization_dedekind : IsDedekindDomain B := by
  letI := primePowerThreePointExtensionInfinity_isGalois p d n E c a
  infer_instance

/-- The reciprocal normalization is finite over its polynomial base. -/
instance primePowerThreePointExtensionInfinityNormalization_finite : Module.Finite E[X] B := by
  letI := primePowerThreePointExtensionInfinity_isGalois p d n E c a
  exact IsIntegralClosure.finite E[X] F L _

/-- The reciprocal normalization is free over the polynomial PID. -/
instance primePowerThreePointExtensionInfinityNormalization_free : Module.Free E[X] B := by
  letI := primePowerThreePointExtensionInfinity_isGalois p d n E c a
  exact IsIntegralClosure.module_free E[X] F L _

/-- The reciprocal normalization recovers the inverted function field as its fraction field. -/
instance primePowerThreePointExtensionInfinityNormalization_fractionRing : IsFractionRing B L :=
  IsIntegralClosure.isFractionRing_of_finite_extension E[X] F L _

/-- The reciprocal normalization has the same fixed covering rank over all extended constants. -/
theorem primePowerThreePointExtensionInfinityNormalization_finrank : Module.finrank E[X] B = M := by
  letI := primePowerThreePointExtensionInfinity_isGalois p d n E c a
  rw [IsIntegralClosure.rank E[X] F L]
  exact primePowerThreePointExtensionInfinity_finrank p d n E c a

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
