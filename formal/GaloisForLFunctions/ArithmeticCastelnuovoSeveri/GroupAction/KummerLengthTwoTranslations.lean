import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLengthTwoModel
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerAdditiveTranslations
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterFields
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Noncyclic automorphisms at geometric length two

When `Q=q^(2n+1)`, the length-two normalized field has an additive model
over the original constants. Translation by the embedded field of order
`q²` gives a faithful elementary abelian subgroup of its automorphisms.
Its order exceeds the characteristic, so the full automorphism group
cannot be cyclic.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
local notation "q" => p ^ (d + 1)
local notation "s" => kummerSquareIndex d (2 * n)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s
local notation "H" => NormalizedKummerField p s d 1
local notation "A" => (Q + 1) / (q + 1) - 1
local notation "F" => KummerAuxiliaryField p s (2 * d + 1 + 1)

private def lengthTwo_primePowerEquiv : KummerLengthTwoField p d n ≃ₐ[K]
    KummerBranchField η⁻¹ (p ^ (2 * d + 1 + 1) - 2) 1 A := by
  have he : p ^ (2 * d + 1 + 1) = q ^ 2 := by
    rw [show 2 * d + 1 + 1 = (d + 1) * 2 by ring, pow_mul]
  rw [he]

private def lengthTwo_additiveEquiv : H ≃ₐ[K]
    KummerBranchField η⁻¹ (p ^ (2 * d + 1 + 1) - 2) 1 A :=
  (normalizedKummerLengthTwoEquiv p d n).trans (lengthTwo_primePowerEquiv p d n)

/-- The quadratic small field translates the length-two model through its explicit field isomorphism. -/
def normalizedKummerLengthTwoTranslationHom : Multiplicative F →* (H ≃ₐ[K] H) :=
  ((lengthTwo_additiveEquiv p d n).symm.autCongr).toMonoidHom.comp
    (kummerAdditiveTranslationAutHom p η⁻¹ (2 * d + 1) A)

/-- Distinct constants induce distinct automorphisms of the original normalized field. -/
theorem normalizedKummerLengthTwoTranslationHom_injective :
    Function.Injective (normalizedKummerLengthTwoTranslationHom p d n) :=
  ((lengthTwo_additiveEquiv p d n).symm.autCongr).injective.comp
    (kummerAdditiveTranslationAutHom_injective p η⁻¹ (2 * d + 1) A)

/-- The embedded quadratic small field has exactly `q²` elements. -/
theorem kummerLengthTwoTranslationParameters_card : Nat.card F = q ^ 2 := by
  have hd : 2 * d + 1 + 1 ∣ 2 * (s + 1) := by
    rw [kummerSquareIndex_succ]
    exact ⟨2 * n + 1, by ring⟩
  rw [kummerAuxiliaryField_card, Nat.gcd_eq_right hd,
    show 2 * d + 1 + 1 = (d + 1) * 2 by ring, pow_mul]

/-- The actual automorphism group contains the constructed subgroup of order `q²`. -/
theorem normalizedKummerLengthTwoTranslationHom_range_card :
    Nat.card (normalizedKummerLengthTwoTranslationHom p d n).range = q ^ 2 := by
  change Nat.card (Set.range (normalizedKummerLengthTwoTranslationHom p d n)) = q ^ 2
  rw [← Nat.card_congr (Equiv.ofInjective _ (normalizedKummerLengthTwoTranslationHom_injective p d n))]
  exact kummerLengthTwoTranslationParameters_card p d n

/-- Every translation has order dividing the characteristic. -/
theorem normalizedKummerLengthTwoTranslationHom_pow_char (a : Multiplicative F) :
    normalizedKummerLengthTwoTranslationHom p d n a ^ p = 1 := by
  rw [← map_pow]
  have hz : a ^ p = 1 := by
    change p • a.toAdd = 0
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [hz, map_one]

private theorem lengthTwo_parameters_not_cyclic : ¬ IsCyclic (Multiplicative F) := by
  intro h
  letI := h
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Multiplicative F)
  have hz : a ^ p = 1 := by
    change p • a.toAdd = 0
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hd : Nat.card F ∣ p := by
    change Nat.card (Multiplicative F) ∣ p
    rw [← ha]
    exact orderOf_dvd_of_pow_eq_one hz
  have hle := Nat.le_of_dvd (Fact.out : p.Prime).pos hd
  rw [kummerLengthTwoTranslationParameters_card, ← pow_mul] at hle
  have hlt := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt
    (by omega : 1 < (d + 1) * 2)
  rw [pow_one] at hlt
  exact Nat.not_lt_of_ge hle hlt

/-- For every odd covering exponent, the full constant-field automorphism group of the length-two normalized curve is noncyclic. -/
theorem normalizedKummerLengthTwo_not_isCyclic : ¬ IsCyclic (H ≃ₐ[K] H) := by
  intro h
  letI := h
  exact lengthTwo_parameters_not_cyclic p d n
    (isCyclic_of_injective (normalizedKummerLengthTwoTranslationHom p d n)
      (normalizedKummerLengthTwoTranslationHom_injective p d n))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
