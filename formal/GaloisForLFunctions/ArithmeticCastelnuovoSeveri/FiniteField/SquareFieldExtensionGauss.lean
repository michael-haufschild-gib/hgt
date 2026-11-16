import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterFields
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldSemiprimitiveGauss
import Mathlib.NumberTheory.LegendreSymbol.Complex

/-!
# Gauss evaluation over every finite extension of the Kummer constants

The chosen trace-zero unit embeds into every finite extension of the
specified square constant field. Its Frobenius equation, the extension
degree, and nontriviality of the prime-field additive character discharge
the inputs of the semiprimitive Gauss evaluation.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (E : Type*) [Field E] [Fintype E]
    [Algebra (SquareConstantField p s) E]
local notation "K" => SquareConstantField p s

/-- Every nontrivial norm-degree character over a finite extension of the stated constants has the exact signed Gauss value. -/
theorem squareConstantField_extension_gauss (χ : MulChar E ℂ)
    (hχ : χ ≠ 1) (horder : χ ^ (p ^ (s + 1) + 1) = 1) :
    letI : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
    letI : Algebra (ZMod p) E := ZMod.algebra E p
    gaussSum χ (finiteFieldTraceCharacter (L := E)
      (AddChar.FiniteField.primitiveChar_to_Complex (ZMod p))) =
      (-1 : ℂ) ^ (Module.finrank K E + 1) *
        (p : ℂ) ^ ((s + 1) * Module.finrank K E) *
          χ (algebraMap K E (kummerTraceConstant p s : K)) := by
  letI : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  letI : Algebra (ZMod p) E := ZMod.algebra E p
  letI : @IsScalarTower (ZMod p) K E
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    @ZMod.instIsScalarTower p K E _ _ Algebra.toModule Algebra.toModule Algebra.toModule
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
  have hψ : ψ ≠ 1 := by
    intro hz
    have hprim : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod p)
    apply hprim (a := (1 : ZMod p)) one_ne_zero
    ext x
    simp only [AddChar.mulShift_apply, one_mul, hz]
  have hdegree : Module.finrank (ZMod p) E = 2 * ((s + 1) * Module.finrank K E) := by
    have h := Module.finrank_mul_finrank (ZMod p) K E
    rw [squareConstantField_finrank] at h
    exact h.symm.trans (Nat.mul_assoc 2 (s + 1) (Module.finrank K E))
  let η := algebraMap K E (kummerTraceConstant p s : K)
  have hη0 : η ≠ 0 := (Units.map (algebraMap K E).toMonoidHom (kummerTraceConstant p s)).ne_zero
  have hη : η ^ p ^ (s + 1) = -η := by
    change (algebraMap K E (kummerTraceConstant p s : K)) ^ p ^ (s + 1) = _
    rw [← map_pow, kummerTraceConstant_frobenius, map_neg]
  exact finiteField_semiprimitive_gauss p (s + 1) (Module.finrank K E) ψ hψ E
    hdegree χ hχ horder η hη0 hη

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
