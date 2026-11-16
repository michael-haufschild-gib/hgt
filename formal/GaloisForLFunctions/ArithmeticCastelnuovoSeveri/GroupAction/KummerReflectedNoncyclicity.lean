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

/-- The complementary length-two parameters also have noncyclic full constant-field automorphism groups. -/
theorem normalizedKummerReflectedLengthTwo_not_isCyclic
    (p : ℕ) [Fact p.Prime] (d n : ℕ) :
    ¬ IsCyclic
      (NormalizedKummerField p (kummerSquareIndex d (2 * (n + 1))) d (4 * n + 3)
        ≃ₐ[SquareConstantField p (kummerSquareIndex d (2 * (n + 1)))]
      NormalizedKummerField p (kummerSquareIndex d (2 * (n + 1))) d (4 * n + 3)) := by
  have e := normalizedKummerReflectionEquiv p d (2 * (n + 1)) ⟨1, by omega⟩
  rw [show 2 * (2 * (n + 1)) - 1 = 4 * n + 3 by omega] at e
  intro h
  letI := h
  exact normalizedKummerLengthTwo_not_isCyclic p d (n + 1)
    (isCyclic_of_injective e.autCongr.toMonoidHom e.autCongr.injective)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
