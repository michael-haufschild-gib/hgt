import GaloisForLFunctions.ConjugateDiagonalGeometry.XiPositiveSourceMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceTransformGrowth
import GaloisForLFunctions.ArithmeticPolarization.ThePriceOfEllipticLocalization

/-!
# Source tests with moving ordinate and translation

Ordinate modulation and real translation remain in the compact C² source-test
space. Their entire transforms agree with the explicit two-parameter functions
used by the Cauchy bounds. These identities keep both operations on the source
test, before any divisor evaluation.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open ArithmeticPolarization

/-- Compact source test localized near a variable ordinate. -/
def sourceTwist (τ : ℝ) (f : CompactTest) : CompactTest :=
  ⟨twist τ f.1, contDiff_twist f.2.1 τ, hasCompactSupport_twist f.2.2 τ⟩

theorem sourceTranslate_add (u v : ℝ) (f : CompactTest) :
    sourceTranslate u (sourceTranslate v f) = sourceTranslate (v + u) f := by
  apply Subtype.ext
  funext x
  change f.1 ((x - u) - v) = f.1 (x - (v + u))
  congr 1
  ring

@[simp] theorem sourceTranslate_zero (f : CompactTest) : sourceTranslate 0 f = f := by
  apply Subtype.ext
  funext x
  change f.1 (x - 0) = f.1 x
  rw [sub_zero]

@[simp] theorem sourceTwist_zero (f : CompactTest) : sourceTwist 0 f = f := by
  apply Subtype.ext
  funext x
  simp only [sourceTwist, twist, Complex.ofReal_zero, zero_mul, neg_zero,
    Complex.exp_zero, one_mul]

/-- The two-parameter Cauchy family is the transform of the actual moved source test. -/
theorem tr_sourceTranslate_sourceTwist (f : CompactTest) (u τ : ℝ) :
    tr (sourceTranslate u (sourceTwist τ f)).1 = shiftedSourceTransform f u τ := by
  funext z
  simp only [sourceTranslate, sourceTwist, tr_translate, tr_twist, shiftedSourceTransform]

end GaloisForLFunctions.ConjugateDiagonalGeometry
