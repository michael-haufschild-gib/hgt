import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.HTGeometry.GeometricTailMass
import GaloisForLFunctions.HTGeometry.WoldThermofieldStandardForm

/-!
# Sprinkling identities for geometric tails

Closed exact specializations of the sprinkling mechanism from arXiv:2603.03257.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Geometric law with one-half success probability. -/
def supercriticalHalfSuccessProbability : unitInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

/-- Geometric law with three-quarter success probability. -/
def supercriticalThreeQuarterSuccessProbability : unitInterval :=
  ⟨3 / 4, by constructor <;> norm_num⟩

/-- Raising success probability from `1/2` to `3/4` squares every failure-tail probability. -/
theorem geometricMeasure_threeQuarter_tail_eq_sq_half_tail (m : ℕ) :
    geometricMeasure supercriticalThreeQuarterSuccessProbability {k : ℕ | m ≤ k} =
      geometricMeasure supercriticalHalfSuccessProbability {k : ℕ | m ≤ k} ^ 2 := by
  rw [geometricMeasure_Ici
      (p := supercriticalThreeQuarterSuccessProbability) (by
        intro h
        have := congrArg Subtype.val h
        norm_num [supercriticalThreeQuarterSuccessProbability] at this),
    geometricMeasure_Ici
      (p := supercriticalHalfSuccessProbability) (by
        intro h
        have := congrArg Subtype.val h
        norm_num [supercriticalHalfSuccessProbability] at this)]
  have hthree : 1 - (supercriticalThreeQuarterSuccessProbability : ℝ) = 1 / 4 := by
    norm_num [supercriticalThreeQuarterSuccessProbability]
  have hhalf : 1 - (supercriticalHalfSuccessProbability : ℝ) = 1 / 2 := by
    norm_num [supercriticalHalfSuccessProbability]
  rw [hthree, hhalf]
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ (1 / 2 : ℝ) ^ m)]
  congr 1
  rw [pow_two, ← mul_pow]
  norm_num

/-- Pointwise sprinkling identity for the corpus's Wold geometric occupation law.  Quarter-discount
mass is half-discount mass multiplied by the exponentially decaying likelihood ratio. -/
theorem geometricOccupationProbability_quarter_eq_sprinkled_half (k : ℕ) :
    geometricOccupationProbability (1 / 4) k =
      (3 / 2) * (1 / 2) ^ k * geometricOccupationProbability (1 / 2) k := by
  have hpow : (1 / 4 : ℝ) ^ k = (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  rw [geometricOccupationProbability, geometricOccupationProbability, hpow]
  ring

end

end GaloisForLFunctions.HTGeometry
