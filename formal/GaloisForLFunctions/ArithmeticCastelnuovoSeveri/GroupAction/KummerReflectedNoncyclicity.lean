import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerReflectionEquivalence
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GroupAction.KummerLengthTwoTranslations

/-!
# Noncyclicity at the reflected length-two parameters

For odd covering exponent `2n+3`, reflection carries geometric length
two to length `4n+4`. Conjugation transports the noncyclic translation
subgroup to this complementary parameter over the same constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
local notation "s" => kummerSquareIndex d (2 * (n + 1))
local notation "K" => SquareConstantField p s
local notation "H" => NormalizedKummerField p s d (4 * n + 3)
local notation "F" => KummerAuxiliaryField p s (2 * d + 1 + 1)

private def reflectedLengthTwoEquiv : NormalizedKummerField p s d 1 ≃ₐ[K] H := by
  have e := normalizedKummerReflectionEquiv p d (2 * (n + 1)) ⟨1, by omega⟩
  rw [show 2 * (2 * (n + 1)) - 1 = 4 * n + 3 by omega] at e
  exact e

/-- Reflection transports the quadratic small-field translations to the complementary parameter. -/
def normalizedKummerReflectedLengthTwoTranslationHom : Multiplicative F →* (H ≃ₐ[K] H) :=
  (reflectedLengthTwoEquiv p d n).autCongr.toMonoidHom.comp
    (normalizedKummerLengthTwoTranslationHom p d (n + 1))

/-- The transported translations still act faithfully. -/
theorem normalizedKummerReflectedLengthTwoTranslationHom_injective :
    Function.Injective (normalizedKummerReflectedLengthTwoTranslationHom p d n) :=
  (reflectedLengthTwoEquiv p d n).autCongr.injective.comp
    (normalizedKummerLengthTwoTranslationHom_injective p d (n + 1))

/-- The complementary member contains an actual automorphism subgroup of order `q²`. -/
theorem normalizedKummerReflectedLengthTwoTranslationHom_range_card :
    Nat.card (normalizedKummerReflectedLengthTwoTranslationHom p d n).range =
      (p ^ (d + 1)) ^ 2 := by
  change Nat.card (Set.range (normalizedKummerReflectedLengthTwoTranslationHom p d n)) = _
  rw [← Nat.card_congr (Equiv.ofInjective _
    (normalizedKummerReflectedLengthTwoTranslationHom_injective p d n))]
  exact kummerLengthTwoTranslationParameters_card p d (n + 1)

/-- Every transported translation has order dividing the characteristic. -/
theorem normalizedKummerReflectedLengthTwoTranslationHom_pow_char (a : Multiplicative F) :
    normalizedKummerReflectedLengthTwoTranslationHom p d n a ^ p = 1 := by
  change (reflectedLengthTwoEquiv p d n).autCongr
    (normalizedKummerLengthTwoTranslationHom p d (n + 1) a) ^ p = 1
  rw [← map_pow, normalizedKummerLengthTwoTranslationHom_pow_char, map_one]

/-- The complementary length-two parameters also have noncyclic full constant-field automorphism groups. -/
theorem normalizedKummerReflectedLengthTwo_not_isCyclic :
    ¬ IsCyclic
      (NormalizedKummerField p (kummerSquareIndex d (2 * (n + 1))) d (4 * n + 3)
        ≃ₐ[SquareConstantField p (kummerSquareIndex d (2 * (n + 1)))]
      NormalizedKummerField p (kummerSquareIndex d (2 * (n + 1))) d (4 * n + 3)) := by
  intro h
  letI := h
  exact normalizedKummerLengthTwo_not_isCyclic p d (n + 1)
    (isCyclic_of_injective (reflectedLengthTwoEquiv p d n).autCongr.toMonoidHom
      (reflectedLengthTwoEquiv p d n).autCongr.injective)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
