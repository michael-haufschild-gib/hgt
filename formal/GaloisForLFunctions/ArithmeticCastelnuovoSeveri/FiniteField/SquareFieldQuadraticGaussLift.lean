import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterFields
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldQuadraticGaussLift
import Mathlib.NumberTheory.LegendreSymbol.Complex

/-!
# Quadratic Gauss lifting in the Kummer constant field

The middle Frobenius fixed field has half the prime-field degree of the
stated square constant field. Its canonical complex additive character
therefore gives the negative-square Gauss lifting identity, with the
extension degree and nontriviality both proved for these actual fields.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "E" => SquareConstantField p s
local notation "K" => KummerAuxiliaryField p s (s + 1)

/-- The stated square constant field has degree two over its middle Frobenius fixed field. -/
theorem squareConstantField_middle_finrank : Module.finrank K E = 2 := by
  have hcK : Nat.card K = p ^ (s + 1) := by
    rw [kummerAuxiliaryField_card, Nat.gcd_eq_right (dvd_mul_left (s + 1) 2)]
  have hcE : Nat.card E = p ^ (2 * (s + 1)) := squareConstantField_card p s
  have hc := Module.natCard_eq_pow_finrank (K := K) (V := E)
  rw [hcE, hcK] at hc
  have he : p ^ (2 * (s + 1)) = (p ^ (s + 1)) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm 2 (s + 1)]
  rw [he] at hc
  exact (Nat.pow_right_injective
    (Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt) hc).symm

/-- Every multiplicative character of the actual middle field satisfies quadratic Gauss lifting for its canonical additive character. -/
theorem squareConstantField_quadratic_gauss_lift (χ : MulChar K ℂ) :
    letI : Fintype K := Fintype.ofFinite K
    letI : Fintype E := Fintype.ofFinite E
    let ψ := AddChar.FiniteField.primitiveChar_to_Complex K
    (∑ x : E, χ (Algebra.norm K x) * ψ (Algebra.trace K E x)) = -((gaussSum χ ψ) ^ 2) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype E := Fintype.ofFinite E
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex K
  change (∑ x : E, χ (Algebra.norm K x) * ψ (Algebra.trace K E x)) = -((gaussSum χ ψ) ^ 2)
  apply finiteField_quadratic_gauss_lift (squareConstantField_middle_finrank p s) χ ψ
  right
  intro hψ
  have hprim : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive K
  apply hprim (a := (1 : K)) one_ne_zero
  ext x
  simp only [AddChar.mulShift_apply, one_mul, hψ]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
