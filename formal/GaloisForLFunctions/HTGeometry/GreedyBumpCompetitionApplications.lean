import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Expected local/remote maximum decomposition

Section 9's pointwise maximum identity is lifted to an exact expectation law.
Integrability is carried by a probability-model structure, leaving closed
theorem statements and no independence assumption.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Integrable signal-associated and remote competing maxima. -/
structure GreedyBumpCompetitionLaw (Ω : Type*) [MeasurableSpace Ω] where
  probability : ProbabilityMeasure Ω
  baseline : ℝ
  localMaximum : Ω → ℝ
  remoteMaximum : Ω → ℝ
  localIntegrable : Integrable localMaximum probability
  correctionIntegrable : Integrable
    (fun ω ↦ max (remoteMaximum ω - localMaximum ω) 0) probability

/-- Expected excess of the global maximum over baseline. -/
def GreedyBumpCompetitionLaw.globalBias
    {Ω : Type*} [MeasurableSpace Ω] (M : GreedyBumpCompetitionLaw Ω) : ℝ :=
  ∫ ω, max (M.localMaximum ω) (M.remoteMaximum ω) - M.baseline ∂M.probability

/-- Expected signal-associated local contribution. -/
def GreedyBumpCompetitionLaw.localBias
    {Ω : Type*} [MeasurableSpace Ω] (M : GreedyBumpCompetitionLaw Ω) : ℝ :=
  ∫ ω, M.localMaximum ω - M.baseline ∂M.probability

/-- Expected positive excess contributed by a remote competitor. -/
def GreedyBumpCompetitionLaw.remoteCorrection
    {Ω : Type*} [MeasurableSpace Ω] (M : GreedyBumpCompetitionLaw Ω) : ℝ :=
  ∫ ω, max (M.remoteMaximum ω - M.localMaximum ω) 0 ∂M.probability

/-- Exact expectation decomposition, without local/remote independence. -/
theorem greedyBump_expected_globalBias_decomposition
    {Ω : Type*} [MeasurableSpace Ω] (M : GreedyBumpCompetitionLaw Ω) :
    M.globalBias = M.localBias + M.remoteCorrection := by
  unfold GreedyBumpCompetitionLaw.globalBias
    GreedyBumpCompetitionLaw.localBias
    GreedyBumpCompetitionLaw.remoteCorrection
  simp_rw [greedyBump_max_decomposition]
  rw [integral_add]
  · exact M.localIntegrable.sub (integrable_const M.baseline)
  · exact M.correctionIntegrable

/-- Remote-peak competition contributes a nonnegative expected correction. -/
theorem greedyBump_expected_remoteCorrection_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (M : GreedyBumpCompetitionLaw Ω) :
    0 ≤ M.remoteCorrection := by
  unfold GreedyBumpCompetitionLaw.remoteCorrection
  exact integral_nonneg fun ω ↦
    greedyBump_remote_correction_nonneg (M.localMaximum ω) (M.remoteMaximum ω)

/-- Consequently global bias is never below the signal-associated local bias. -/
theorem greedyBump_expected_localBias_le_globalBias
    {Ω : Type*} [MeasurableSpace Ω] (M : GreedyBumpCompetitionLaw Ω) :
    M.localBias ≤ M.globalBias := by
  rw [greedyBump_expected_globalBias_decomposition]
  exact le_add_of_nonneg_right (greedyBump_expected_remoteCorrection_nonneg M)

end

end GaloisForLFunctions.HTGeometry
