import GaloisForLFunctions.HTGeometry.NonMarkovianLangevinKernel
import GaloisForLFunctions.HTGeometry.CharacteristicFunctionPositiveDefinite
import Mathlib.Tactic

open MeasureTheory
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every bundled probability law supplies a canonical stationary memory kernel. -/
def probabilityMemoryKernel (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  charFun (μ : Measure ℝ) t

@[simp]
theorem probabilityMemoryKernel_zero (μ : ProbabilityMeasure ℝ) :
    probabilityMemoryKernel μ 0 = 1 := by
  simp [probabilityMemoryKernel, charFun_zero]

theorem probabilityMemoryKernel_neg (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    probabilityMemoryKernel μ (-t) = star (probabilityMemoryKernel μ t) := by
  exact charFun_neg t

theorem norm_probabilityMemoryKernel_le_zero
    (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    ‖probabilityMemoryKernel μ t‖ ≤ 1 := by
  exact norm_charFun_le_one t

theorem positiveDefiniteOnReal_probabilityMemoryKernel
    (μ : ProbabilityMeasure ℝ) :
    PositiveDefiniteOnReal (probabilityMemoryKernel μ) :=
  positiveDefiniteOnReal_charFun (μ : Measure ℝ)

/-- Compound-Poisson jump environments form a closed family of memory kernels. -/
def compoundPoissonMemoryKernel
    (intensity : ℝ≥0) (jump : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  charFun (compoundPoisson (intensity : ℝ) (jump : Measure ℝ)) t

theorem compoundPoissonMemoryKernel_eq_exp
    (intensity : ℝ≥0) (jump : ProbabilityMeasure ℝ) (t : ℝ) :
    compoundPoissonMemoryKernel intensity jump t =
      Complex.exp ((intensity : ℂ) *
        (probabilityMemoryKernel jump t - 1)) := by
  exact charFun_compoundPoisson (intensity : ℝ) intensity.property
    (jump : Measure ℝ) t

@[simp]
theorem compoundPoissonMemoryKernel_zero
    (intensity : ℝ≥0) (jump : ProbabilityMeasure ℝ) :
    compoundPoissonMemoryKernel intensity jump 0 = 1 := by
  rw [compoundPoissonMemoryKernel_eq_exp]
  simp

theorem compoundPoissonMemoryKernel_neg
    (intensity : ℝ≥0) (jump : ProbabilityMeasure ℝ) (t : ℝ) :
    compoundPoissonMemoryKernel intensity jump (-t) =
      star (compoundPoissonMemoryKernel intensity jump t) := by
  letI : IsProbabilityMeasure
      (compoundPoisson (intensity : ℝ) (jump : Measure ℝ)) :=
    isProbabilityMeasure_compoundPoisson
      (intensity : ℝ) intensity.property (jump : Measure ℝ)
  exact charFun_neg t

theorem norm_compoundPoissonMemoryKernel_le_zero
    (intensity : ℝ≥0) (jump : ProbabilityMeasure ℝ) (t : ℝ) :
    ‖compoundPoissonMemoryKernel intensity jump t‖ ≤ 1 := by
  letI : IsProbabilityMeasure
      (compoundPoisson (intensity : ℝ) (jump : Measure ℝ)) :=
    isProbabilityMeasure_compoundPoisson
      (intensity : ℝ) intensity.property (jump : Measure ℝ)
  exact norm_charFun_le_one t

theorem positiveDefiniteOnReal_compoundPoissonMemoryKernel
    (intensity : ℝ≥0) (jump : ProbabilityMeasure ℝ) :
    PositiveDefiniteOnReal (compoundPoissonMemoryKernel intensity jump) :=
  positiveDefiniteOnReal_charFun_compoundPoisson
    (intensity : ℝ) intensity.property (jump : Measure ℝ)

end

end GaloisForLFunctions.HTGeometry

