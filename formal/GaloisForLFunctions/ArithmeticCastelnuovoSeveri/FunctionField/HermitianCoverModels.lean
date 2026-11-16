import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianCoverGalois
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerReflectionEquivalence
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerTraceChoice

/-!
# Hermitian covers under coefficient changes and exponent reflection

Composing a covering with a constant-field isomorphism preserves its
actual image field. Hence both changes of trace-zero coefficient and
reflection of the exponent preserve the constructed Galois Hermitian
cover and its exact degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d r m : ℕ)
local notation "s" => hermitianKummerCoverIndex d r m
local notation "K" => SquareConstantField p s
local notation "H" => HermitianKummerField p s
local notation "R" => kummerExponent (p ^ (d + 1)) (r + 1)
local notation "φ" => normalizedKummerHermitianEmbedding p d r m

/-- Every nonzero trace-zero coefficient choice admits the same Hermitian cover. -/
def traceChoiceKummerHermitianEmbedding (η : KummerTraceChoices p s) :
    SquareKummerField p s (η.val⁻¹ ^ R) (p ^ (d + 1) - 2) R →ₐ[K] H :=
  (φ).comp (kummerTraceChoiceEquiv p s η (p ^ (d + 1) - 2) R).symm.toAlgHom

/-- The changed-coefficient covering is an embedding of the actual fields. -/
theorem traceChoiceKummerHermitianEmbedding_injective (η : KummerTraceChoices p s) :
    Function.Injective (traceChoiceKummerHermitianEmbedding p d r m η) :=
  (traceChoiceKummerHermitianEmbedding p d r m η).injective

/-- Coefficient rescaling preserves the actual subfield inside the Hermitian source. -/
theorem traceChoiceKummerHermitianEmbedding_fieldRange (η : KummerTraceChoices p s) :
    (traceChoiceKummerHermitianEmbedding p d r m η).fieldRange = (φ).fieldRange := by
  rw [traceChoiceKummerHermitianEmbedding, ← AlgHom.map_fieldRange,
    AlgEquiv.fieldRange_eq_top, ← AlgHom.fieldRange_eq_map]

/-- The exact covering degree holds for every trace-zero coefficient choice. -/
theorem traceChoiceKummerHermitianEmbedding_finrank (η : KummerTraceChoices p s) :
    Module.finrank (traceChoiceKummerHermitianEmbedding p d r m η).fieldRange H =
      p ^ ((d + 1) * (r + 1) * m) * R := by
  rw [traceChoiceKummerHermitianEmbedding_fieldRange]
  exact normalizedKummerHermitianEmbedding_finrank p d r m

/-- The Hermitian cover for every trace-zero coefficient choice is Galois. -/
theorem traceChoiceKummerHermitianEmbedding_isGalois (η : KummerTraceChoices p s) :
    IsGalois (traceChoiceKummerHermitianEmbedding p d r m η).fieldRange H := by
  rw [traceChoiceKummerHermitianEmbedding_fieldRange]
  exact normalizedKummerHermitianEmbedding_isGalois p d r m

private def coverReflectionParameter : Fin (2 * ((r + 1) * (m + 1) - 1) + 1) :=
  ⟨r, by
    have h : (r + 1) * (m + 1) = r + 1 + (r + 1) * m := by ring
    omega⟩

/-- Reflecting the exponent gives an embedding of the complementary normalized Kummer model. -/
def reflectedKummerHermitianEmbedding :
    NormalizedKummerField p s d (2 * ((r + 1) * (m + 1) - 1) - r) →ₐ[K] H :=
  (φ).comp (normalizedKummerReflectionEquiv p d ((r + 1) * (m + 1) - 1)
    (coverReflectionParameter r m)).symm.toAlgHom

/-- The reflected covering is an embedding of actual function fields. -/
theorem reflectedKummerHermitianEmbedding_injective :
    Function.Injective (reflectedKummerHermitianEmbedding p d r m) :=
  (reflectedKummerHermitianEmbedding p d r m).injective

/-- Reflection preserves the subfield inside the Hermitian source. -/
theorem reflectedKummerHermitianEmbedding_fieldRange :
    (reflectedKummerHermitianEmbedding p d r m).fieldRange = (φ).fieldRange := by
  rw [reflectedKummerHermitianEmbedding, ← AlgHom.map_fieldRange,
    AlgEquiv.fieldRange_eq_top, ← AlgHom.fieldRange_eq_map]

/-- The reflected cover has the same exact extension degree. -/
theorem reflectedKummerHermitianEmbedding_finrank :
    Module.finrank (reflectedKummerHermitianEmbedding p d r m).fieldRange H =
      p ^ ((d + 1) * (r + 1) * m) * R := by
  rw [reflectedKummerHermitianEmbedding_fieldRange]
  exact normalizedKummerHermitianEmbedding_finrank p d r m

/-- The reflected Hermitian trace cover is Galois over its actual image subfield. -/
theorem reflectedKummerHermitianEmbedding_isGalois :
    IsGalois (reflectedKummerHermitianEmbedding p d r m).fieldRange H := by
  rw [reflectedKummerHermitianEmbedding_fieldRange]
  exact normalizedKummerHermitianEmbedding_isGalois p d r m

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
