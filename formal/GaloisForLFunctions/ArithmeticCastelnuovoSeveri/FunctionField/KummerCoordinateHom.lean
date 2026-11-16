import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalSubcover

/-!
# Homomorphisms from actual Kummer coordinates

A transcendental coordinate and a radical satisfying the defining
branch equation determine a homomorphism from the Kummer function
field. Localization supplies the rational base map, and adjoining the
root supplies the field map with the prescribed generator images.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial GaloisForLFunctions.HTGeometry
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
variable (c : Kˣ) (b R n : ℕ) (u v : E) (hu : Transcendental K u)
    (hv : v ^ (n + 1) = algebraMap K E c * u * (1 - u ^ (b + 1)) ^ R)

include hv in
private theorem kummerCoordinates_eval :
    (kummerBranchFieldPolynomial c b R n).eval₂ (fracRealize hu) v = 0 := by
  change (X ^ (n + 1) - C (algebraMap K[X] (FractionRing K[X])
    (kummerBranch c b R))).eval₂ (fracRealize hu) v = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change v ^ (n + 1) - fracRealize hu
    (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R)) = 0
  rw [fracRealize_algebraMap, kummerBranch]
  simp only [map_mul, map_pow, map_sub, map_one, aeval_C, aeval_X]
  exact sub_eq_zero.mpr hv

/-- A transcendental coordinate and a solution of the branch equation define an actual constant-field homomorphism. -/
def kummerBranchFieldHomOfCoordinates : KummerBranchField c b R n →ₐ[K] E :=
  AdjoinRoot.liftAlgHom _ (fracRealize hu) v (kummerCoordinates_eval c b R n u v hu hv)

/-- The homomorphism sends the rational coordinate to the specified transcendental element. -/
theorem kummerBranchFieldHomOfCoordinates_coordinate :
    kummerBranchFieldHomOfCoordinates c b R n u v hu hv
      (algebraMap K[X] (KummerBranchField c b R n) X) = u := by
  rw [IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]), AdjoinRoot.algebraMap_eq,
    kummerBranchFieldHomOfCoordinates, AdjoinRoot.liftAlgHom_of, fracRealize_algebraMap, aeval_X]

/-- The homomorphism sends the named radical to the specified solution. -/
theorem kummerBranchFieldHomOfCoordinates_root :
    kummerBranchFieldHomOfCoordinates c b R n u v hu hv
      (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) = v :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
