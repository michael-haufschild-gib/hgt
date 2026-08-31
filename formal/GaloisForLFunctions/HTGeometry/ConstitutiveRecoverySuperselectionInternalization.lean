import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift
import GaloisForLFunctions.HTGeometry.PrimePoissonSourceLinearSuperselection

/-!
# Common recovery and source superselection
-/

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two measures define the same measure class. -/
def MeasureClassEquivalent {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) : Prop := μ ≪ ν ∧ ν ≪ μ

section CommonRecovery

variable {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]

/-- A common nonzero conditional recovery reflects absolute continuity exactly. -/
theorem splitFormation_absolutelyContinuous_iff
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ] :
    splitFormation μ κ ≪ splitFormation ν κ ↔ μ ≪ ν := by
  exact Measure.absolutelyContinuous_compProd_left_iff

/-- A common Markov recovery reflects equality of measure class exactly. -/
theorem splitFormation_measureClassEquivalent_iff
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ] :
    MeasureClassEquivalent (splitFormation μ κ) (splitFormation ν κ) ↔
      MeasureClassEquivalent μ ν := by
  simp only [MeasureClassEquivalent, splitFormation_absolutelyContinuous_iff]

/-- A common Markov recovery reflects mutual singularity exactly. -/
theorem splitFormation_mutuallySingular_iff
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ] :
    splitFormation μ κ ⟂ₘ splitFormation ν κ ↔ μ ⟂ₘ ν := by
  exact Measure.mutuallySingular_compProd_left_iff

/-- A measurable-embedding observer action followed by common recovery cannot merge singular
source sectors. -/
theorem formationLiftKernel_mutuallySingular
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ]
    (A : X → X) (hA : MeasurableEmbedding A)
    (hμν : μ ⟂ₘ ν) :
    formationLiftKernel κ A hA.measurable ∘ₘ splitFormation μ κ ⟂ₘ
      formationLiftKernel κ A hA.measurable ∘ₘ splitFormation ν κ := by
  rw [formationLiftKernel_naturality μ κ A hA.measurable,
    formationLiftKernel_naturality ν κ A hA.measurable]
  exact (hA.mutuallySingular_map hμν).compProd_of_left κ κ

end CommonRecovery

section PrimeReflection

variable {H : Type*} [MeasurableSpace H]

/-- Common recovery leaves the reflected prime-Poisson measure-class wall exactly at the critical
half-density. -/
theorem primePoisson_splitFormation_measureClassEquivalent_iff
    (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (κ : Kernel PrimeTorus H) [IsMarkovKernel κ] :
    MeasureClassEquivalent
        (splitFormation (primePoissonMeasure σ t hσ) κ)
        (splitFormation (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) κ) ↔
      σ = 1 / 2 := by
  rw [splitFormation_measureClassEquivalent_iff]
  exact primePoissonMeasure_reflection_mutuallyAbsolutelyContinuous_iff σ t hσ hσ1

/-- Off the critical wall, every common recovered prime-Poisson packet remains in a disjoint
source sector. -/
theorem primePoisson_splitFormation_mutuallySingular_of_ne_half
    (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) (hwall : σ ≠ 1 / 2)
    (κ : Kernel PrimeTorus H) [IsMarkovKernel κ] :
    splitFormation (primePoissonMeasure σ t hσ) κ ⟂ₘ
      splitFormation (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) κ := by
  exact (splitFormation_mutuallySingular_iff
    (primePoissonMeasure σ t hσ)
    (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) κ).2
      (primePoissonMeasure_reflection_mutuallySingular_of_ne_half σ t hσ hσ1 hwall)

/-- Even after a measurable-embedding functional action, common recovery cannot merge reflected
off-wall prime sectors. -/
theorem primePoisson_formationLift_mutuallySingular_of_ne_half
    (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) (hwall : σ ≠ 1 / 2)
    (κ : Kernel PrimeTorus H) [IsMarkovKernel κ]
    (A : PrimeTorus → PrimeTorus) (hA : MeasurableEmbedding A) :
    formationLiftKernel κ A hA.measurable ∘ₘ
        splitFormation (primePoissonMeasure σ t hσ) κ ⟂ₘ
      formationLiftKernel κ A hA.measurable ∘ₘ
        splitFormation (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) κ := by
  exact formationLiftKernel_mutuallySingular
    (primePoissonMeasure σ t hσ)
    (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) κ A hA
    (primePoissonMeasure_reflection_mutuallySingular_of_ne_half σ t hσ hσ1 hwall)

/-- **External/internal reflection classification.**  Reflected recovered prime packets share a
measure class exactly when a nonzero closed source-linear reflected sewing exists. -/
theorem primePoisson_recovery_internalization_iff
    (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (κ : Kernel PrimeTorus H) [IsMarkovKernel κ] :
    MeasureClassEquivalent
        (splitFormation (primePoissonMeasure σ t hσ) κ)
        (splitFormation (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) κ) ↔
      NonzeroClosedSourceLinearSewing
        (continuousL2Mul (primePoissonMeasure σ t hσ))
        (continuousL2Mul
          (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1))) := by
  rw [primePoisson_splitFormation_measureClassEquivalent_iff σ t hσ hσ1 κ,
    primePoisson_reflection_nonzeroClosedSourceLinearSewing_iff σ t hσ hσ1]

/-- Bundled capstone: common recovery preserves measure class and singularity, and the literal
prime reflection is internally implementable exactly on the critical wall. -/
theorem recoverySuperselectionInternalization_capstone
    (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (κ : Kernel PrimeTorus H) [IsMarkovKernel κ] :
    (MeasureClassEquivalent
          (splitFormation (primePoissonMeasure σ t hσ) κ)
          (splitFormation (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) κ) ↔
        σ = 1 / 2) ∧
      (NonzeroClosedSourceLinearSewing
          (continuousL2Mul (primePoissonMeasure σ t hσ))
          (continuousL2Mul
            (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1))) ↔
        σ = 1 / 2) ∧
      (σ ≠ 1 / 2 →
        splitFormation (primePoissonMeasure σ t hσ) κ ⟂ₘ
          splitFormation (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) κ) := by
  exact ⟨primePoisson_splitFormation_measureClassEquivalent_iff σ t hσ hσ1 κ,
    primePoisson_reflection_nonzeroClosedSourceLinearSewing_iff σ t hσ hσ1,
    fun hwall =>
      primePoisson_splitFormation_mutuallySingular_of_ne_half σ t hσ hσ1 hwall κ⟩

end PrimeReflection

end

end GaloisForLFunctions.HTGeometry
