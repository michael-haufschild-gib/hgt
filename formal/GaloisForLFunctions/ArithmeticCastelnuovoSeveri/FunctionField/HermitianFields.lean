import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTraceConstants
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTangentFactor
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators

/-!
# The Hermitian function field and its generic point

The trace-zero change of variable converts the actual Kummer field to
`v^(Q+1)=u^Q+u`. Both coordinates generate the field, and the additive
coordinate is transcendental over the specified square constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s

/-- The Hermitian function field over the specified square constant field. -/
abbrev HermitianKummerField := SquareKummerField p s η⁻¹ (Q - 2) 1
local notation "H" => HermitianKummerField p s

/-- The additive Hermitian coordinate is the polynomial coordinate divided by the trace constant. -/
def hermitianKummerAdditiveCoordinate : H :=
  algebraMap K H ((η : K)⁻¹) * algebraMap K[X] H X

/-- The multiplicative Hermitian coordinate is the named Kummer radical. -/
def hermitianKummerRadicalCoordinate : H :=
  AdjoinRoot.root (kummerBranchFieldPolynomial η⁻¹ (Q - 2) 1 Q)

/-- Multiplication by the trace constant recovers the polynomial coordinate. -/
theorem hermitianKummerAdditiveCoordinate_recover :
    algebraMap K H (η : K) * hermitianKummerAdditiveCoordinate p s = algebraMap K[X] H X := by
  rw [hermitianKummerAdditiveCoordinate, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (kummerTraceConstant p s).ne_zero,
    map_one, one_mul]

/-- The constructed field satisfies the usual Hermitian equation over its actual constants. -/
theorem hermitianKummerField_equation :
    AdjoinRoot.root (kummerBranchFieldPolynomial η⁻¹ (Q - 2) 1 Q) ^ (Q + 1) =
      hermitianKummerAdditiveCoordinate p s ^ Q + hermitianKummerAdditiveCoordinate p s := by
  let y := algebraMap K[X] H X
  have hQ : 2 ≤ Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hbranch : y * (1 - y ^ (Q - 2 + 1)) = y - y ^ Q := by
    rw [show Q - 2 + 1 = Q - 1 by omega, mul_sub, mul_one, ← pow_succ',
      Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  have hroot : AdjoinRoot.root (kummerBranchFieldPolynomial η⁻¹ (Q - 2) 1 Q) ^ (Q + 1) =
      algebraMap K H (η : K)⁻¹ * (y - y ^ Q) := by
    rw [kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply, kummerBranch]
    simp only [map_mul, map_pow, map_sub, map_one, pow_one, Units.val_inv_eq_inv_val]
    change algebraMap K H (η : K)⁻¹ * y * (1 - y ^ (Q - 2 + 1)) = _
    rw [mul_assoc, hbranch]
  have hη : ((η : K)⁻¹) ^ Q = -(η : K)⁻¹ := by
    rw [inv_pow, kummerTraceConstant_frobenius, inv_neg]
  have hηmap := congrArg (algebraMap K H) hη
  rw [map_pow, map_neg] at hηmap
  rw [hroot]
  change algebraMap K H (η : K)⁻¹ * (y - y ^ Q) =
    (algebraMap K H (η : K)⁻¹ * y) ^ Q + algebraMap K H (η : K)⁻¹ * y
  rw [mul_pow, hηmap]
  ring

/-- The additive Hermitian coordinate is transcendental over the actual constants. -/
theorem hermitianKummerAdditiveCoordinate_transcendental :
    Transcendental K (hermitianKummerAdditiveCoordinate p s) := by
  intro h
  apply kummerBranchField_coordinate_transcendental η⁻¹ (Q - 2) 1 Q
  rw [← hermitianKummerAdditiveCoordinate_recover p s]
  exact (isAlgebraic_algebraMap (R := K) (A := H) (η : K)).mul h

/-- The two field generators form an actual Hermitian point over the function field. -/
def hermitianKummerGenericPoint : HermitianAffinePoint p s H :=
  ⟨(hermitianKummerRadicalCoordinate p s, hermitianKummerAdditiveCoordinate p s),
    (hermitianKummerField_equation p s).symm⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
