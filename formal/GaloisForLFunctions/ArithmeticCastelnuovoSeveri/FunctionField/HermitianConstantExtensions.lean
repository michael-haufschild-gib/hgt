import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFields

/-!
# Hermitian function fields over enlarged constants

Transporting the chosen trace-zero unit preserves the Hermitian equation.
The resulting field and polynomial normalization are actual radical objects
over the enlarged constants; their degree remains `Q+1`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p s) E]
local notation "K" => SquareConstantField p s
local notation "Q" => p ^ (s + 1)

/-- The nonzero trace-zero coefficient transported from the original square field. -/
def hermitianExtensionTraceConstant : Eˣ :=
  Units.mk0 (algebraMap K E (kummerTraceConstant p s : K))
    ((map_ne_zero (algebraMap K E)).mpr (kummerTraceConstant p s).ne_zero)

local notation "η" => hermitianExtensionTraceConstant p s E

/-- The transported unit has the same Frobenius sign. -/
theorem hermitianExtensionTraceConstant_frobenius : (η : E) ^ Q = -(η : E) := by
  change (algebraMap K E (kummerTraceConstant p s : K)) ^ Q =
    -algebraMap K E (kummerTraceConstant p s : K)
  rw [← map_pow, kummerTraceConstant_frobenius, map_neg]

/-- The actual Hermitian radical field over the larger constant field. -/
abbrev HermitianExtensionField := SquareKummerExtensionField p s E η⁻¹ (Q - 2) 1
local notation "H" => HermitianExtensionField p s E

/-- The additive coordinate obtained by dividing the polynomial coordinate by the trace unit. -/
def hermitianExtensionAdditiveCoordinate : H :=
  algebraMap E H ((η : E)⁻¹) * algebraMap E[X] H X

/-- The canonical radical is the first Hermitian coordinate. -/
def hermitianExtensionRadicalCoordinate : H :=
  AdjoinRoot.root (kummerBranchFieldPolynomial η⁻¹ (Q - 2) 1 Q)

/-- The additive coordinate recovers the original polynomial coordinate. -/
theorem hermitianExtensionAdditiveCoordinate_recover :
    algebraMap E H (η : E) * hermitianExtensionAdditiveCoordinate p s E =
      algebraMap E[X] H X := by
  rw [hermitianExtensionAdditiveCoordinate, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (hermitianExtensionTraceConstant p s E).ne_zero, map_one, one_mul]

/-- Both actual coordinates satisfy the Hermitian equation after extending constants. -/
theorem hermitianExtensionField_equation :
    hermitianExtensionRadicalCoordinate p s E ^ (Q + 1) =
      hermitianExtensionAdditiveCoordinate p s E ^ Q +
        hermitianExtensionAdditiveCoordinate p s E := by
  let y := algebraMap E[X] H X
  have hQ : 2 ≤ Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hbranch : y * (1 - y ^ (Q - 2 + 1)) = y - y ^ Q := by
    rw [show Q - 2 + 1 = Q - 1 by omega, mul_sub, mul_one, ← pow_succ',
      Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  have hroot : hermitianExtensionRadicalCoordinate p s E ^ (Q + 1) =
      algebraMap E H (η : E)⁻¹ * (y - y ^ Q) := by
    rw [hermitianExtensionRadicalCoordinate, kummerBranchField_root_pow,
      ← IsScalarTower.algebraMap_apply, kummerBranch]
    simp only [map_mul, map_pow, map_sub, map_one, pow_one, Units.val_inv_eq_inv_val]
    change algebraMap E H (η : E)⁻¹ * y * (1 - y ^ (Q - 2 + 1)) = _
    rw [mul_assoc, hbranch]
  have hη : ((η : E)⁻¹) ^ Q = -(η : E)⁻¹ := by
    rw [inv_pow, hermitianExtensionTraceConstant_frobenius, inv_neg]
  have hηmap := congrArg (algebraMap E H) hη
  rw [map_pow, map_neg] at hηmap
  rw [hroot]
  change algebraMap E H (η : E)⁻¹ * (y - y ^ Q) =
    (algebraMap E H (η : E)⁻¹ * y) ^ Q + algebraMap E H (η : E)⁻¹ * y
  rw [mul_pow, hηmap]
  ring

/-- The additive coordinate remains transcendental over all enlarged constants. -/
theorem hermitianExtensionAdditiveCoordinate_transcendental :
    Transcendental E (hermitianExtensionAdditiveCoordinate p s E) := by
  intro h
  apply kummerBranchField_coordinate_transcendental η⁻¹ (Q - 2) 1 Q
  rw [← hermitianExtensionAdditiveCoordinate_recover p s E]
  exact (isAlgebraic_algebraMap (R := E) (A := H) (η : E)).mul h

/-- The two coordinates define an actual generic point over the extended function field. -/
def hermitianExtensionGenericPoint : HermitianAffinePoint p s H :=
  ⟨(hermitianExtensionRadicalCoordinate p s E,
    hermitianExtensionAdditiveCoordinate p s E), (hermitianExtensionField_equation p s E).symm⟩

/-- The field degree over the polynomial-coordinate rational field remains `Q+1`. -/
theorem hermitianExtensionField_finrank : Module.finrank (FractionRing E[X]) H = Q + 1 :=
  squareKummerExtension_finrank p s E η⁻¹ (Q - 2) 1

/-- The radical equation remains Galois after extending constants. -/
theorem hermitianExtensionField_isGalois : IsGalois (FractionRing E[X]) H :=
  squareKummerExtension_isGalois p s E η⁻¹ (Q - 2) 1

/-- The finite affine normalization in the extended Hermitian function field. -/
abbrev HermitianExtensionNormalization :=
  SquareKummerExtensionNormalization p s E η⁻¹ (Q - 2) 1

/-- The actual normalization has the unchanged covering rank. -/
theorem hermitianExtensionNormalization_finrank :
    Module.finrank E[X] (HermitianExtensionNormalization p s E) = Q + 1 :=
  squareKummerExtensionNormalization_finrank p s E η⁻¹ (Q - 2) 1

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
