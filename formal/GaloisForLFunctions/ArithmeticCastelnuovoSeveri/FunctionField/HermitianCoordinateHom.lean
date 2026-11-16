import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCoordinateHom

/-!
# Hermitian field homomorphisms from coordinates

A Hermitian point with transcendental additive coordinate determines a
homomorphism from the actual Hermitian function field. Restoring the trace
constant converts its equation to the defining Kummer equation.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p s) E]
    (L : Type*) [Field L] [Algebra E L]
local notation "Q" => p ^ (s + 1)
local notation "η" => hermitianExtensionTraceConstant p s E
local notation "H" => HermitianExtensionField p s E
local notation "φ" => algebraMap E L
variable (T : HermitianAffinePoint p s L) (hT : Transcendental E T.val.2)

/-- Restoring the trace unit gives the polynomial coordinate of the target point. -/
def hermitianPointPolynomialCoordinate : L := φ (η : E) * T.val.2

/-- Multiplication by the trace unit preserves transcendence of the additive coordinate. -/
theorem hermitianPointPolynomialCoordinate_transcendental :
    Transcendental E (hermitianPointPolynomialCoordinate p s E L T) := by
  intro h
  have hi := (show IsIntegral E (φ (η : E)⁻¹) from isIntegral_algebraMap).mul h.isIntegral
  have he : φ (η : E)⁻¹ * hermitianPointPolynomialCoordinate p s E L T = T.val.2 := by
    rw [hermitianPointPolynomialCoordinate, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ (hermitianExtensionTraceConstant p s E).ne_zero, map_one, one_mul]
  rw [he] at hi
  exact hT hi.isAlgebraic

private theorem point_branch :
    T.val.1 ^ (Q + 1) =
      φ (η⁻¹ : Eˣ) * hermitianPointPolynomialCoordinate p s E L T *
        (1 - hermitianPointPolynomialCoordinate p s E L T ^ (Q - 2 + 1)) ^ 1 := by
  let w := hermitianPointPolynomialCoordinate p s E L T
  have hQ : 2 ≤ Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hw : w * (1 - w ^ (Q - 2 + 1)) = w - w ^ Q := by
    rw [show Q - 2 + 1 = Q - 1 by omega, mul_sub, mul_one, ← pow_succ',
      Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  change T.val.1 ^ (Q + 1) = φ (η : E)⁻¹ * w * (1 - w ^ (Q - 2 + 1)) ^ 1
  rw [pow_one, mul_assoc, hw]
  have hη : φ (η : E)⁻¹ * φ (η : E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (hermitianExtensionTraceConstant p s E).ne_zero, map_one]
  have hηQ : (φ (η : E)) ^ Q = -φ (η : E) := by
    rw [← map_pow, hermitianExtensionTraceConstant_frobenius, map_neg]
  calc
    T.val.1 ^ (Q + 1) = T.val.2 ^ Q + T.val.2 := T.property.symm
    _ = φ (η : E)⁻¹ * w - φ (η : E)⁻¹ * w ^ Q := by
      change _ = φ (η : E)⁻¹ * (φ (η : E) * T.val.2) -
        φ (η : E)⁻¹ * (φ (η : E) * T.val.2) ^ Q
      rw [mul_pow, hηQ]
      calc
        _ = (φ (η : E)⁻¹ * φ (η : E)) * (T.val.2 ^ Q + T.val.2) := by rw [hη, one_mul]
        _ = _ := by ring
    _ = _ := (mul_sub _ _ _).symm

/-- A transcendental Hermitian point induces a homomorphism of the actual function field. -/
def hermitianFieldHomOfCoordinates : H →ₐ[E] L :=
  kummerBranchFieldHomOfCoordinates η⁻¹ (Q - 2) 1 Q
    (hermitianPointPolynomialCoordinate p s E L T) T.val.1
    (hermitianPointPolynomialCoordinate_transcendental p s E L T hT)
    (point_branch p s E L T)

/-- The polynomial coordinate maps to the trace-normalized target coordinate. -/
theorem hermitianFieldHomOfCoordinates_coordinate :
    hermitianFieldHomOfCoordinates p s E L T hT (algebraMap E[X] H X) =
      hermitianPointPolynomialCoordinate p s E L T :=
  kummerBranchFieldHomOfCoordinates_coordinate _ _ _ _ _ _ _ _

/-- The canonical radical maps to the first coordinate of the target point. -/
theorem hermitianFieldHomOfCoordinates_radical :
    hermitianFieldHomOfCoordinates p s E L T hT
      (hermitianExtensionRadicalCoordinate p s E) = T.val.1 :=
  kummerBranchFieldHomOfCoordinates_root _ _ _ _ _ _ _ _

/-- The additive coordinate maps to the second coordinate of the target point. -/
theorem hermitianFieldHomOfCoordinates_additive :
    hermitianFieldHomOfCoordinates p s E L T hT
      (hermitianExtensionAdditiveCoordinate p s E) = T.val.2 := by
  rw [hermitianExtensionAdditiveCoordinate, map_mul, AlgHom.commutes,
    hermitianFieldHomOfCoordinates_coordinate, hermitianPointPolynomialCoordinate,
    ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ (hermitianExtensionTraceConstant p s E).ne_zero, map_one, one_mul]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
