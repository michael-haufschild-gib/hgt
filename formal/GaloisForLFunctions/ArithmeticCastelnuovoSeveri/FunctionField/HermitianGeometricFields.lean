import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTangentLocalEquation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The geometric Hermitian field and its tangent functions

The constants are the algebraic closure of the specified square field.
Every geometric affine point therefore defines a tangent function in one
actual function field. Its additive equation records both contact factors.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)

/-- Algebraically closed constants for the specified Hermitian curve. -/
abbrev HermitianGeometricConstants := AlgebraicClosure (SquareConstantField p s)
local notation "E" => HermitianGeometricConstants p s

/-- The geometric constants retain the original characteristic. -/
instance hermitianGeometricConstants_charP : CharP E p :=
  charP_of_injective_algebraMap (algebraMap (SquareConstantField p s) E).injective p

/-- The literal Hermitian radical field over algebraically closed constants. -/
abbrev HermitianGeometricField := HermitianExtensionField p s E
local notation "H" => HermitianGeometricField p s

/-- The actual geometric function field has characteristic `p`. -/
instance hermitianGeometricField_charP : CharP H p :=
  charP_of_injective_algebraMap (algebraMap E H).injective p

/-- The geometric covering has degree `Q+1` over its rational coordinate field. -/
theorem hermitianGeometricField_finrank : Module.finrank (FractionRing E[X]) H = Q + 1 :=
  hermitianExtensionField_finrank p s E

/-- The geometric radical covering is Galois. -/
theorem hermitianGeometricField_isGalois : IsGalois (FractionRing E[X]) H :=
  hermitianExtensionField_isGalois p s E

/-- The actual geometric affine normalization. -/
abbrev HermitianGeometricNormalization := HermitianExtensionNormalization p s E

/-- A geometric point viewed as a constant point over the function field. -/
def hermitianGeometricConstantPoint (P : HermitianAffinePoint p s E) :
    HermitianAffinePoint p s H :=
  ⟨(algebraMap E H P.val.1, algebraMap E H P.val.2), by
    simpa only [map_add, map_pow] using congrArg (algebraMap E H) P.property⟩

/-- The tangent at any geometric point, evaluated at the actual generic point. -/
def hermitianGeometricTangentFunction (P : HermitianAffinePoint p s E) : H :=
  hermitianTangentDifference p s H (hermitianGeometricConstantPoint p s P)
    (hermitianExtensionGenericPoint p s E)

/-- The geometric tangent is the usual linear expression in the two actual coordinates. -/
theorem hermitianGeometricTangentFunction_eq (P : HermitianAffinePoint p s E) :
    hermitianGeometricTangentFunction p s P =
      hermitianExtensionAdditiveCoordinate p s E - algebraMap E H P.val.2 -
        algebraMap E H (P.val.1 ^ Q) *
          (hermitianExtensionRadicalCoordinate p s E - algebraMap E H P.val.1) := by
  simp only [hermitianGeometricTangentFunction, hermitianTangentDifference,
    hermitianTangentPolynomial, hermitianGeometricConstantPoint, hermitianExtensionGenericPoint,
    eval_add, eval_mul, eval_sub, eval_C, eval_X, map_pow]
  ring

/-- The tangent equation holds in the actual geometric function field for every geometric point. -/
theorem hermitianGeometricTangentFunction_equation (P : HermitianAffinePoint p s E) :
    hermitianGeometricTangentFunction p s P ^ Q + hermitianGeometricTangentFunction p s P =
      (hermitianExtensionRadicalCoordinate p s E - algebraMap E H P.val.1) ^ Q *
        (hermitianExtensionRadicalCoordinate p s E - algebraMap E H (P.val.1 ^ (Q * Q))) := by
  simpa only [hermitianGeometricTangentFunction, hermitianGeometricConstantPoint,
    hermitianExtensionGenericPoint, map_pow] using
      hermitianTangentDifference_equation p s H (hermitianGeometricConstantPoint p s P)
        (hermitianExtensionGenericPoint p s E)

/-- The radical coordinate differs from every geometric constant. -/
theorem hermitianGeometricRadical_sub_ne_zero (a : E) :
    hermitianExtensionRadicalCoordinate p s E - algebraMap E H a ≠ 0 := by
  intro h
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  let f : E[X] := X ^ Q + X - C (a ^ (Q + 1))
  have hf : f ≠ 0 := by
    intro hf0
    have hc := congrArg (fun g : E[X] => g.coeff Q) hf0
    simp only [f, coeff_sub, coeff_add, coeff_X_pow_self, coeff_X,
      if_neg (Ne.symm (ne_of_gt hQ)), coeff_C,
      if_neg (ne_of_gt (Nat.zero_lt_of_lt hQ)), add_zero, sub_zero, coeff_zero] at hc
    exact one_ne_zero hc
  have heq := hermitianExtensionField_equation p s E
  rw [sub_eq_zero.mp h, ← map_pow] at heq
  have heval : aeval (hermitianExtensionAdditiveCoordinate p s E) f = 0 := by
    simp only [f, map_sub, map_add, map_pow, aeval_X, aeval_C]
    exact sub_eq_zero.mpr heq.symm
  exact hf ((transcendental_iff.mp
    (hermitianExtensionAdditiveCoordinate_transcendental p s E)) f heval)

/-- Every geometric tangent is a nonzero rational function on the actual curve. -/
theorem hermitianGeometricTangentFunction_ne_zero (P : HermitianAffinePoint p s E) :
    hermitianGeometricTangentFunction p s P ≠ 0 := by
  intro h
  have heq := hermitianGeometricTangentFunction_equation p s P
  rw [h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), zero_add] at heq
  rcases mul_eq_zero.mp heq.symm with hleft | hright
  · exact hermitianGeometricRadical_sub_ne_zero p s P.val.1
      (eq_zero_of_pow_eq_zero hleft)
  · exact hermitianGeometricRadical_sub_ne_zero p s (P.val.1 ^ (Q * Q)) hright

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
