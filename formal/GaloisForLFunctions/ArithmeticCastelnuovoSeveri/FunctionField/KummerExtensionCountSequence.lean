import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLiteralExtensionCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerConstantTensorPlaces
import Mathlib.FieldTheory.Finite.Extension

/-!
# The actual sequence of Kummer extension point counts

Choose a finite constant extension of every positive degree and count
all rational valuation places of the fixed equation there. The tensor
identification realizes these as genuine constant extensions of the
original function field. Degree zero is assigned zero for the ghost
series convention.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "h" => s + 1
local notation "K" => SquareConstantField p s
local notation "Q" => p ^ h
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "η" => kummerTraceConstant p s
local notation "c₀" => η⁻¹ ^ R
local notation "L" => SquareKummerField p s c₀ (q - 2) R
local notation "g" => Module.finrank K (globalRegularDifferentials K L)

/-- The fixed equation over the selected extension is the literal tensor extension of the original field. -/
def primePowerKummerLiteralTensorEquiv (E : Type*) [Field E] [Algebra K E]
    [FiniteDimensional K E] :
    (E ⊗[K] L) ≃ₐ[E]
      PrimePowerKummerLiteralExtensionField p d n r E (Units.map (algebraMap K E).toMonoidHom η) := by
  have e := kummerConstantTensorEquiv K E c₀ (q - 2) R Q
  have hc : Units.map (algebraMap K E).toMonoidHom c₀ =
      (Units.map (algebraMap K E).toMonoidHom η)⁻¹ ^ R := by
    rw [map_pow, map_inv]
  rw [hc] at e
  exact e

/-- The actual number of rational places over the chosen extension of each positive degree. -/
def primePowerKummerExtensionPointCount (e : ℕ) : ℕ :=
  if he : e = 0 then 0 else
    letI : NeZero e := ⟨he⟩
    let E := FiniteField.Extension K p e
    Nat.card (RationalConstantFieldPlaces E
      (PrimePowerKummerLiteralExtensionField p d n r E (Units.map (algebraMap K E).toMonoidHom η)))

/-- Degree zero is omitted from the point-count ghost sequence. -/
theorem primePowerKummerExtensionPointCount_zero : primePowerKummerExtensionPointCount p d n r 0 = 0 := by
  rw [primePowerKummerExtensionPointCount, dif_pos rfl]

/-- The extension count is the number of actual rational places on the literal scalar tensor field. -/
theorem primePowerKummerExtensionPointCount_tensor (e : ℕ) [NeZero e] :
    primePowerKummerExtensionPointCount p d n r e =
      Nat.card (KummerConstantTensorRationalPlaces K (FiniteField.Extension K p e) c₀ (q - 2) R Q) := by
  rw [primePowerKummerExtensionPointCount, dif_neg (NeZero.ne e)]
  let E := FiniteField.Extension K p e
  have hcount :=
    kummerConstantTensor_rationalPlaces_card K (FiniteField.Extension K p e) c₀ (q - 2) R Q
  have hc : Units.map (algebraMap K E).toMonoidHom c₀ =
      (Units.map (algebraMap K E).toMonoidHom η)⁻¹ ^ R := by
    rw [map_pow, map_inv]
  rw [hc] at hcount
  exact hcount.symm

/-- Every positive extension degree has the exact signed count, with twice the actual differential dimension. -/
theorem primePowerKummerExtensionPointCount_eq (e : ℕ) [NeZero e] :
    (primePowerKummerExtensionPointCount p d n r e : ℂ) =
      ((Q : ℂ) ^ 2) ^ e + 1 - (2 * g : ℕ) * (-(Q : ℂ)) ^ e := by
  let E := FiniteField.Extension K p e
  letI := Fintype.ofFinite E
  have hc := primePowerKummer_literal_extension_rationalPlaces_card p d n r E
  have hrank : Module.finrank K E = e := FiniteField.finrank_extension K p e
  have hcard : (Fintype.card E : ℂ) = ((Q : ℂ) ^ 2) ^ e := by
    rw [← Nat.card_eq_fintype_card]
    change (Nat.card (FiniteField.Extension K p e) : ℂ) = _
    rw [FiniteField.natCard_extension, squareConstantField_card]
    simp only [Nat.cast_pow]
    rw [Nat.mul_comm 2 h, pow_mul]
  rw [hrank, hcard] at hc
  rw [primePowerKummerExtensionPointCount, dif_neg (NeZero.ne e)]
  change (Nat.card (RationalConstantFieldPlaces E
    (PrimePowerKummerLiteralExtensionField p d n r E (Units.map (algebraMap K E).toMonoidHom η))) : ℂ) = _
  rw [hc]
  have hpower : (p : ℂ) ^ (h * e) = (Q : ℂ) ^ e := by
    simpa only [Nat.cast_pow] using (pow_mul (p : ℂ) h e)
  rw [hpower, pow_succ (-1 : ℂ) e, neg_eq_neg_one_mul (Q : ℂ), mul_pow]
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
