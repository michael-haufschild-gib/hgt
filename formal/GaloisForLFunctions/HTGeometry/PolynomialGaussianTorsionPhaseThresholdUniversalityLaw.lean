import GaloisForLFunctions.HTGeometry.GaussianTorsionLanguageTailLock
import GaloisForLFunctions.HTGeometry.PolynomialTorsionLanguageEntireSeries

/-!
# Polynomial--Gaussian torsion-phase threshold universality

The polynomial-magnitude theorem proves torsion-language hypertranscendence above exponent two.
The Gaussian tail-lock theorem independently resolves the unbounded critical face at exponent two.
Their explicit entire carriers coincide at that boundary, closing the two regimes into one sharp
law for every real exponent at least two.
-/

namespace GaloisForLFunctions

open Filter PowerSeries
open scoped Topology

noncomputable section

/-- At exponent two, the polynomial-magnitude entire carrier is exactly the Gaussian carrier. -/
theorem polynomialTorsionLanguageFunction_two_eq_gaussianPhaseFunction
    (B : ℝ) (u : ℕ → ℂ) :
    polynomialTorsionLanguageFunction B 2 u = gaussianPhaseFunction B u := by
  funext z
  rw [polynomialTorsionLanguageFunction_eq_tsum,
    gaussianPhaseFunction_eq_tsum]
  apply tsum_congr
  intro n
  simp [gaussianPhaseCoeff]

/-- **Polynomial--Gaussian threshold law.**  Every unit-norm torsion-language-universal phase
makes the explicit entire series with coefficient magnitudes `exp (-B n^β)`
hypertranscendental throughout the closed range `β ≥ 2`.  The boundary `β = 2` is supplied by
Gaussian tail lock; the strict range is supplied by polynomial confinement. -/
theorem hypertranscendental_polynomialTorsionLanguageFunction_of_two_le
    {B β : ℝ} (hB : 0 < B) (hβ : 2 ≤ β)
    {u : ℕ → ℂ} (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : TorsionLanguageUniversal u) :
    Hypertranscendental (polynomialTorsionLanguageFunction B β u) := by
  by_cases hcritical : β = 2
  · subst β
    rw [polynomialTorsionLanguageFunction_two_eq_gaussianPhaseFunction]
    exact hypertranscendental_gaussianPhaseFunction hB huNorm hu
  · have hsupercritical : 2 < β := lt_of_le_of_ne hβ (Ne.symm hcritical)
    exact hypertranscendental_polynomialTorsionLanguageFunction
      hB hsupercritical huNorm hu

/-- The one explicit universal torsion phase simultaneously realizes the complete closed
polynomial--Gaussian exponent range. -/
theorem hypertranscendental_universalUnit_polynomialTorsionLanguageFunction_of_two_le
    {B β : ℝ} (hB : 0 < B) (hβ : 2 ≤ β) :
    Hypertranscendental
      (polynomialTorsionLanguageFunction B β universalUnitTorsionPhase) :=
  hypertranscendental_polynomialTorsionLanguageFunction_of_two_le
    hB hβ universalUnitTorsionPhase_norm
      universalUnitTorsionPhase_torsionLanguageUniversal

end


end GaloisForLFunctions
