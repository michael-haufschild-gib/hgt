import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.SquareFieldExtensionGauss
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerGaussCharacterCount
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldFrobeniusJacobi

/-!
# Weighted Jacobi values over extensions of the Kummer constants

The branch exponent is a Frobenius power minus one, so the Jacobi sum
equals the Gauss sum of the powered character. The trace-zero coefficient
cancels its Gauss character factor. Every nontrivial full cyclic
character therefore contributes either `-1` or the same signed middle
field size, according to whether its powered character is trivial.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "m" => p ^ (d + 1) - 1
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "M" => primePowerKummerCyclicDegree p d n
variable (E : Type*) [Field E] [Fintype E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
local notation "H" => unitEndomorphismCharacters («R» := ℂ) (powMonoidHom M : Eˣ →* Eˣ)

/-- The trace-zero three-point coefficient after the given extension of constants. -/
def primePowerKummerExtensionCoefficient : Eˣ :=
  (Units.map (algebraMap K E).toMonoidHom (kummerTraceConstant p s))⁻¹ ^ (m * R)

/-- Every nontrivial cyclic character contributes either the trivial Gauss value or the uniform signed extension-field value. -/
theorem primePowerKummer_extension_weighted_jacobi (ρ : H) (hρ : ρ.val ≠ 1) :
    ρ.val (primePowerKummerExtensionCoefficient p d n r E : E) *
      jacobiSum ρ.val (ρ.val ^ (m * R)) =
        if ρ.val ^ (m * R) = 1 then -1 else
          (-1 : ℂ) ^ (Module.finrank K E + 1) *
            (p : ℂ) ^ ((s + 1) * Module.finrank K E) := by
  classical
  letI : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  letI : Algebra (ZMod p) E := ZMod.algebra E p
  letI : @IsScalarTower (ZMod p) K E
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    @ZMod.instIsScalarTower p K E _ _ Algebra.toModule Algebra.toModule Algebra.toModule
  let η := Units.map (algebraMap K E).toMonoidHom (kummerTraceConstant p s)
  let χ := ρ.val
  let φ := χ ^ (m * R)
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
  have hψ : ψ ≠ 1 := by
    intro hz
    have hprim : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod p)
    apply hprim (a := (1 : ZMod p)) one_ne_zero
    ext x
    simp only [AddChar.mulShift_apply, one_mul, hz]
  have hroot : χ ^ M = 1 := (mem_powerEndomorphismCharacters_iff M χ).mp ρ.property
  have hφorder : φ ^ (p ^ (s + 1) + 1) = 1 := by
    change (χ ^ (m * R)) ^ (p ^ (s + 1) + 1) = 1
    have hexp : (m * R) * (p ^ (s + 1) + 1) = M * R := by
      dsimp only [primePowerKummerCyclicDegree]
      ring
    rw [← pow_mul, hexp, pow_mul, hroot, one_pow]
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hdegree := kummerInfinity_primePower_poleDegree p d r
  rw [show p ^ (d + 1) - 2 + 1 = m by omega, ← pow_mul] at hdegree
  have hexp : p ^ ((d + 1) * r) - 1 = m * R := by omega
  have hj : jacobiSum χ φ = gaussSum φ (finiteFieldTraceCharacter (L := E) ψ) := by
    have h := finiteField_jacobiSum_frobenius («K» := ZMod p) χ hρ ψ hψ ((d + 1) * r)
    rw [ZMod.card, hexp] at h
    exact h
  have hcancel : χ (primePowerKummerExtensionCoefficient p d n r E : E) * φ (η : E) = 1 := by
    have hunit : χ.toUnitHom (η⁻¹ ^ (m * R)) * χ.toUnitHom (η ^ (m * R)) = 1 := by
      rw [← map_mul, ← mul_pow, inv_mul_cancel, one_pow, map_one]
    have hv := congrArg Units.val hunit
    change χ (primePowerKummerExtensionCoefficient p d n r E : E) *
      χ ((η ^ (m * R) : Eˣ) : E) = 1 at hv
    have hηpow : χ ((η ^ (m * R) : Eˣ) : E) = φ (η : E) := by
      change χ ((η : E) ^ (m * R)) = (χ ^ (m * R)) (η : E)
      rw [map_pow, MulChar.pow_apply_coe]
    rw [hηpow] at hv
    exact hv
  change χ (primePowerKummerExtensionCoefficient p d n r E : E) * jacobiSum χ φ =
    if φ = 1 then -1 else _
  by_cases hφ : φ = 1
  · rw [if_pos hφ, hj, hφ,
      gaussSum_one_left ((finiteFieldTraceCharacter_ne_one_iff ψ).mpr hψ)]
    have hc : χ (primePowerKummerExtensionCoefficient p d n r E : E) = 1 := by
      simpa only [hφ, MulChar.one_apply_coe, mul_one] using hcancel
    rw [hc, one_mul]
  · rw [if_neg hφ, hj, squareConstantField_extension_gauss p s E φ hφ hφorder]
    change χ (primePowerKummerExtensionCoefficient p d n r E : E) *
      ((-1 : ℂ) ^ (Module.finrank K E + 1) *
        (p : ℂ) ^ ((s + 1) * Module.finrank K E) * φ (η : E)) = _
    calc
      _ = ((-1 : ℂ) ^ (Module.finrank K E + 1) *
          (p : ℂ) ^ ((s + 1) * Module.finrank K E)) *
          (χ (primePowerKummerExtensionCoefficient p d n r E : E) * φ (η : E)) := by ring
      _ = _ := by rw [hcancel, mul_one]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
