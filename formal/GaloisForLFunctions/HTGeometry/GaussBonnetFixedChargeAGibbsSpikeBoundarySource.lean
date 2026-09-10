import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeDimensionalLimits
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# The exact Jordan decomposition at the dimensional source boundary

The positive error consists of the two retained atoms; the negative error
is the missing mass at the zero-rate atom. Their supports are disjoint.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

def egbFixedChargeAGibbsSpikeBoundaryMass : NNReal := ⟨1 / 4, by norm_num⟩

def egbFixedChargeAGibbsSpikeBoundarySource : Measure HausdorffSourceSpace :=
  hausdorffAtomSource egbFixedChargeAGibbsSpikeBoundaryMass egbFixedChargeAGibbsCollisionZeroNode

instance : IsFiniteMeasure egbFixedChargeAGibbsSpikeBoundarySource := by
  unfold egbFixedChargeAGibbsSpikeBoundarySource
  infer_instance

def egbFixedChargeAGibbsSpikeBoundaryPositivePart (n : ℕ) : Measure HausdorffSourceSpace :=
  hausdorffAtomSource (egbFixedChargeAGibbsFullCollisionSlowMass n 1 (egbFixedChargeAGibbsSpikeEnergy n))
      egbFixedChargeAGibbsCollisionSlowNode +
  hausdorffAtomSource (egbFixedChargeAGibbsFullCollisionFastMass n 1 (egbFixedChargeAGibbsSpikeEnergy n))
      egbFixedChargeAGibbsCollisionFastNode

def egbFixedChargeAGibbsSpikeBoundaryDeficitMass (n : ℕ) : NNReal :=
  ⟨5 / (4 * (2 : ℝ) ^ (n + 3)), by positivity⟩

def egbFixedChargeAGibbsSpikeBoundaryNegativePart (n : ℕ) : Measure HausdorffSourceSpace :=
  hausdorffAtomSource (egbFixedChargeAGibbsSpikeBoundaryDeficitMass n) egbFixedChargeAGibbsCollisionZeroNode

instance (n : ℕ) : IsFiniteMeasure (egbFixedChargeAGibbsSpikeBoundaryPositivePart n) := by
  unfold egbFixedChargeAGibbsSpikeBoundaryPositivePart
  infer_instance

instance (n : ℕ) : IsFiniteMeasure (egbFixedChargeAGibbsSpikeBoundaryNegativePart n) := by
  unfold egbFixedChargeAGibbsSpikeBoundaryNegativePart
  infer_instance

private theorem boundary_parts_singular (n : ℕ) :
    Measure.MutuallySingular (egbFixedChargeAGibbsSpikeBoundaryPositivePart n)
      (egbFixedChargeAGibbsSpikeBoundaryNegativePart n) := by
  have hr : egbFixedChargeAGibbsCollisionSlowNode ≠ egbFixedChargeAGibbsCollisionZeroNode := by
    intro h
    have hv := congrArg (fun y : HausdorffSourceSpace => (y : ℝ)) h
    norm_num [egbFixedChargeAGibbsCollisionSlowNode, egbFixedChargeAGibbsCollisionZeroNode] at hv
  have hs : egbFixedChargeAGibbsCollisionFastNode ≠ egbFixedChargeAGibbsCollisionZeroNode := by
    intro h
    have hv := congrArg (fun y : HausdorffSourceSpace => (y : ℝ)) h
    norm_num [egbFixedChargeAGibbsCollisionFastNode, egbFixedChargeAGibbsCollisionZeroNode] at hv
  refine ⟨{egbFixedChargeAGibbsCollisionZeroNode}, measurableSet_singleton _, ?_, ?_⟩
  · simp [egbFixedChargeAGibbsSpikeBoundaryPositivePart, hausdorffAtomSource, hr, hs]
  · simp [egbFixedChargeAGibbsSpikeBoundaryNegativePart, hausdorffAtomSource]

/-- The literal Jordan pair of the spike source error. -/
def egbFixedChargeAGibbsSpikeBoundaryJordan (n : ℕ) : JordanDecomposition HausdorffSourceSpace where
  posPart := egbFixedChargeAGibbsSpikeBoundaryPositivePart n
  negPart := egbFixedChargeAGibbsSpikeBoundaryNegativePart n
  mutuallySingular := boundary_parts_singular n

/-- Signed difference between the actual finite source and its dimensional boundary. -/
def egbFixedChargeAGibbsSpikeBoundaryError (n : ℕ) : SignedMeasure HausdorffSourceSpace :=
  (egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)).toSignedMeasure -
    egbFixedChargeAGibbsSpikeBoundarySource.toSignedMeasure

/-- Adding the missing endpoint mass balances the finite source against the boundary and positive retained mass. -/
theorem egbFixedChargeAGibbsSpikeBoundarySource_balance (n : ℕ) :
    egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n) +
      egbFixedChargeAGibbsSpikeBoundaryNegativePart n =
    egbFixedChargeAGibbsSpikeBoundaryPositivePart n + egbFixedChargeAGibbsSpikeBoundarySource := by
  have hm : egbFixedChargeAGibbsFullCollisionErasedMass n 1 (egbFixedChargeAGibbsSpikeEnergy n) +
      egbFixedChargeAGibbsSpikeBoundaryDeficitMass n = egbFixedChargeAGibbsSpikeBoundaryMass := by
    apply Subtype.ext
    change egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) +
      5 / (4 * (2 : ℝ) ^ (n + 3)) = 1 / 4
    rw [egbFixedChargeAGibbsSpike_discarded_energy]
    have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hn]
    <;> ring
  simp only [egbFixedChargeAGibbsFullCollisionHausdorffSource,
    egbFixedChargeAGibbsSpikeBoundaryPositivePart, egbFixedChargeAGibbsSpikeBoundaryNegativePart,
    egbFixedChargeAGibbsSpikeBoundarySource, hausdorffAtomSource]
  rw [← hm, add_smul]
  abel

private theorem boundary_error_eq_jordan (n : ℕ) :
    egbFixedChargeAGibbsSpikeBoundaryError n = (egbFixedChargeAGibbsSpikeBoundaryJordan n).toSignedMeasure := by
  have h := Measure.toSignedMeasure_congr (egbFixedChargeAGibbsSpikeBoundarySource_balance n)
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add] at h
  change (egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)).toSignedMeasure -
    egbFixedChargeAGibbsSpikeBoundarySource.toSignedMeasure =
    (egbFixedChargeAGibbsSpikeBoundaryPositivePart n).toSignedMeasure -
    (egbFixedChargeAGibbsSpikeBoundaryNegativePart n).toSignedMeasure
  exact sub_eq_sub_iff_add_eq_add.mpr h

/-- The actual signed source difference has exactly the explicit positive and negative atomic parts. -/
theorem egbFixedChargeAGibbsSpikeBoundaryError_jordan (n : ℕ) :
    (egbFixedChargeAGibbsSpikeBoundaryError n).toJordanDecomposition =
      egbFixedChargeAGibbsSpikeBoundaryJordan n := by
  exact SignedMeasure.toJordanDecomposition_eq (boundary_error_eq_jordan n)

/-- Total variation is the literal sum of the two retained atoms and the endpoint deficit atom. -/
theorem egbFixedChargeAGibbsSpikeBoundaryError_totalVariation (n : ℕ) :
    (egbFixedChargeAGibbsSpikeBoundaryError n).totalVariation =
      egbFixedChargeAGibbsSpikeBoundaryPositivePart n + egbFixedChargeAGibbsSpikeBoundaryNegativePart n := by
  rw [SignedMeasure.totalVariation, egbFixedChargeAGibbsSpikeBoundaryError_jordan]
  rfl

/-- The boundary source has exactly the limiting full-history moments. -/
theorem egbFixedChargeAGibbsSpikeBoundarySource_moment (m : ℕ) :
    hausdorffMoment egbFixedChargeAGibbsSpikeBoundarySource m = (0 : ℝ) ^ m / 4 := by
  rw [egbFixedChargeAGibbsSpikeBoundarySource, hausdorffMoment_atom]
  change (1 / 4 : ℝ) * (0 : ℝ) ^ m = (0 : ℝ) ^ m / 4
  ring

/-- Every full-source moment converges to the corresponding moment of the literal boundary measure. -/
theorem egbFixedChargeAGibbsSpike_source_moments_tendsto_boundary (m : ℕ) :
    Filter.Tendsto (fun n : ℕ => hausdorffMoment
      (egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)) m)
      Filter.atTop (nhds (hausdorffMoment egbFixedChargeAGibbsSpikeBoundarySource m)) := by
  simpa only [egbFixedChargeAGibbsFullCollisionHausdorffSource_moment,
    egbFixedChargeAGibbsSpikeBoundarySource_moment] using egbFixedChargeAGibbsSpike_full_collision_limit m

end
end GaloisForLFunctions.HTGeometry
