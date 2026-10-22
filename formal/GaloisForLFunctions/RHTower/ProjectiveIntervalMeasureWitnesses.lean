import GaloisForLFunctions.RHTower.Suzuki.SuzukiDonoghueKernelUniformBound

/-!
# Probability measures on the projective interval exist

The Donoghue–Herglotz layer is stated for a probability measure on the compact projective interval,
and nothing exhibited one.  The interval is a nondegenerate closed interval around the origin, so it
is nonempty, and the Dirac mass at its centre is a probability measure on it.

Consequently the transform laws are not statements about an empty class of measures, and the
finiteness premise follows from the probability premise wherever both are asked for.
-/

open MeasureTheory

namespace GaloisForLFunctions
namespace RHTower

/-- The origin is a phase of the projective interval. -/
theorem zero_mem_projectiveInterval : (0 : ℝ) ∈ projectiveInterval := by
  rw [projectiveInterval, Set.mem_Icc]
  have hpi := Real.pi_pos
  constructor <;> linarith

/-- The centre of the projective interval. -/
def projectiveIntervalCentre : ↥projectiveInterval := ⟨0, zero_mem_projectiveInterval⟩

instance nonemptyProjectiveIntervalCentre : Nonempty ↥projectiveInterval := ⟨projectiveIntervalCentre⟩

/-- **The Dirac mass at the centre is a probability measure on the projective interval.** -/
theorem exists_isProbabilityMeasure_projectiveInterval :
    ∃ nu : Measure ↥projectiveInterval, IsProbabilityMeasure nu :=
  ⟨Measure.dirac projectiveIntervalCentre, inferInstance⟩

/-- Hence a finite measure on the projective interval exists as well. -/
theorem exists_isFiniteMeasure_projectiveInterval :
    ∃ nu : Measure ↥projectiveInterval, IsFiniteMeasure nu := by
  obtain ⟨nu, hnu⟩ := exists_isProbabilityMeasure_projectiveInterval
  haveI := hnu
  exact ⟨nu, inferInstance⟩

/-- Every probability measure on the projective interval is finite. -/
theorem isFiniteMeasure_of_isProbabilityMeasure_projectiveInterval
    (nu : Measure ↥projectiveInterval) [IsProbabilityMeasure nu] : IsFiniteMeasure nu :=
  inferInstance

end RHTower
end GaloisForLFunctions
