import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusKummerFields
import Mathlib.FieldTheory.Relrank


/-!
# The actual rational coordinate subfield

Realizing rational functions at the Frobenius radical coordinate is the canonical
base embedding. Its image is the coordinate subfield, and the radical
extension has its stated degree over this actual intermediate field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
open GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] (c : Kˣ) (b R n : ℕ)

/-- Rational realization at the coordinate agrees with the given base-field embedding. -/
theorem frobeniusKummerField_fracRealize_coordinate :
    fracRealize (frobeniusKummerField_coordinate_transcendental c b R n) =
      IsScalarTower.toAlgHom K (FractionRing K[X]) (FrobeniusKummerField c b R n) := by
  apply AlgHom.ext
  intro x
  obtain ⟨f, g, _, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) x
  rw [map_div₀, fracRealize_algebraMap, fracRealize_algebraMap,
    frobeniusKummerField_aeval_coordinate]
  change algebraMap K[X] (FrobeniusKummerField c b R n) f /
    algebraMap K[X] (FrobeniusKummerField c b R n) g =
    algebraMap (FractionRing K[X]) (FrobeniusKummerField c b R n)
      (algebraMap K[X] (FractionRing K[X]) f / algebraMap K[X] (FractionRing K[X]) g)
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- The radical degree is unchanged when the rational base is viewed as its actual coordinate subfield. -/
theorem frobeniusKummerField_coordinate_finrank :
    Module.finrank K⟮algebraMap K[X] (FrobeniusKummerField c b R n) X⟯
      (FrobeniusKummerField c b R n) = n + 1 := by
  let L := FrobeniusKummerField c b R n
  let e := fracRealizeEquiv (frobeniusKummerField_coordinate_transcendental c b R n)
  have h := Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl L) (by
    apply RingHom.ext
    intro x
    change (e x : L) = algebraMap (FractionRing K[X]) L x
    rw [fracRealizeEquiv_apply, frobeniusKummerField_fracRealize_coordinate]
    rfl)
  exact h.symm.trans (frobeniusKummerField_finrank c b R n)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
