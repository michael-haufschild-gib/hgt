import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullConeLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConeMeasureBoundary

/-! # Actual weak measure collapse with arbitrary exact positive source survivors -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter

private theorem integrable_atom (w : NNReal) (z : HausdorffSourceSpace)
    (f : HausdorffSourceSpace → ℝ) : Integrable f (hausdorffAtomSource w z) := by
  unfold hausdorffAtomSource
  change Integrable f ((w : ENNReal) • Measure.dirac z)
  exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

private theorem integral_atom (w : NNReal) (z : HausdorffSourceSpace)
    (f : HausdorffSourceSpace → ℝ) :
    ∫ t, f t ∂hausdorffAtomSource w z = (w : ℝ) * f z := by
  simp [hausdorffAtomSource, NNReal.smul_def]

/-- Every real test is integrable against every point of the three-atom positive cone. -/
theorem egbFixedChargeAGibbsFullConeSource_integrable (R A B : NNReal) (f : HausdorffSourceSpace → ℝ) :
    Integrable f (egbFixedChargeAGibbsFullConeSource R A B) := by
  exact integrable_add_measure.mpr ⟨integrable_atom R _ f, egbFixedChargeAGibbsConeSource_integrable A B f⟩

/-- A cone source evaluates any real test by exactly its three prescribed atomic masses. -/
theorem egbFixedChargeAGibbsFullConeSource_integral (R A B : NNReal) (f : HausdorffSourceSpace → ℝ) :
    ∫ z, f z ∂egbFixedChargeAGibbsFullConeSource R A B =
      (R : ℝ) * f egbFixedChargeAGibbsCollisionZeroNode + (A : ℝ) * f egbFixedChargeAGibbsCollisionSlowNode + (B : ℝ) * f egbFixedChargeAGibbsCollisionFastNode := by
  unfold egbFixedChargeAGibbsFullConeSource
  rw [integral_add_measure (integrable_atom R _ f) (egbFixedChargeAGibbsConeSource_integrable A B f),
    integral_atom, egbFixedChargeAGibbsConeSource_integral]
  ring

/-- Every actual source test is the exact positive scaling of its prescribed cone-source test. -/
theorem egbFixedChargeAGibbsFullCone_source_integral (n k : ℕ) (R A B : NNReal)
    (f : HausdorffSourceSpace → ℝ) :
    ∫ z, f z ∂egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      (egbFixedChargeAGibbsFullConeScale n k R A B : ℝ) *
        ((R : ℝ) * f egbFixedChargeAGibbsCollisionZeroNode + (A : ℝ) * f egbFixedChargeAGibbsCollisionSlowNode + (B : ℝ) * f egbFixedChargeAGibbsCollisionFastNode) := by
  rw [egbFixedChargeAGibbsFullCone_source_factorization, ← egbFixedChargeAGibbsFullConeSource_scale,
    egbFixedChargeAGibbsFullConeSource_integral]
  change ((egbFixedChargeAGibbsFullConeScale n k R A B : ℝ) * R) * _ +
    ((egbFixedChargeAGibbsFullConeScale n k R A B : ℝ) * A) * _ +
    ((egbFixedChargeAGibbsFullConeScale n k R A B : ℝ) * B) * _ = _
  ring

/-- Actual source integrals tend to zero for every real test, without continuity or boundedness assumptions. -/
theorem egbFixedChargeAGibbsFullCone_source_integrals_tendsto_zero (n : ℕ) (R A B : NNReal)
    (f : HausdorffSourceSpace → ℝ) :
    Tendsto (fun k => ∫ z, f z ∂egbFixedChargeAGibbsFullCollisionHausdorffSource n 1
      (egbFixedChargeAGibbsFullConeEnergy n k R A B)) atTop (nhds 0) := by
  have h := (egbFixedChargeAGibbsFullConeScale_tendsto_zero n R A B).mul_const
    ((R : ℝ) * f egbFixedChargeAGibbsCollisionZeroNode + (A : ℝ) * f egbFixedChargeAGibbsCollisionSlowNode + (B : ℝ) * f egbFixedChargeAGibbsCollisionFastNode)
  simpa only [egbFixedChargeAGibbsFullCone_source_integral, zero_mul] using h

/-- The actual finite positive measure, with its weak topology retained by a named definition. -/
def egbFixedChargeAGibbsFullConeFiniteSource (n k : ℕ) (R A B : NNReal) : FiniteMeasure HausdorffSourceSpace :=
  ⟨egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B), inferInstance⟩

/-- Every prescribed cone point is the exact rescaled survivor of actual finite measures converging weakly to zero. -/
theorem egbFixedChargeAGibbsFullCone_source_weak_tendsto_zero (n : ℕ) (R A B : NNReal) :
    Tendsto (fun k => egbFixedChargeAGibbsFullConeFiniteSource n k R A B) atTop (nhds 0) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun k => ∫ z, f z ∂egbFixedChargeAGibbsFullCollisionHausdorffSource n 1
    (egbFixedChargeAGibbsFullConeEnergy n k R A B)) atTop (nhds (∫ z, f z ∂(0 : Measure HausdorffSourceSpace)))
  simpa using egbFixedChargeAGibbsFullCone_source_integrals_tendsto_zero n R A B f

end
end GaloisForLFunctions.HTGeometry
