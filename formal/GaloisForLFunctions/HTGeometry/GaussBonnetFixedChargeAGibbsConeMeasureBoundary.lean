import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConeLimits
import Mathlib.MeasureTheory.Measure.FiniteMeasure

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

/-- Every real test is integrable against every point of the two-atom positive cone. -/
theorem egbFixedChargeAGibbsConeSource_integrable (x y : NNReal) (f : HausdorffSourceSpace → ℝ) :
    Integrable f (egbFixedChargeAGibbsConeSource x y) := by
  exact integrable_add_measure.mpr ⟨integrable_atom x _ f, integrable_atom y _ f⟩

/-- A cone source evaluates any real test by exactly its two prescribed atomic masses. -/
theorem egbFixedChargeAGibbsConeSource_integral (x y : NNReal) (f : HausdorffSourceSpace → ℝ) :
    ∫ z, f z ∂egbFixedChargeAGibbsConeSource x y =
      (x : ℝ) * f egbFixedChargeAGibbsCollisionSlowNode + (y : ℝ) * f egbFixedChargeAGibbsCollisionFastNode := by
  unfold egbFixedChargeAGibbsConeSource
  rw [integral_add_measure (integrable_atom x _ f) (integrable_atom y _ f), integral_atom, integral_atom]

/-- Every actual source test is the exact positive scaling of its prescribed cone-source test. -/
theorem egbFixedChargeAGibbsCone_source_integral (n k m : ℕ) (x y : NNReal)
    (f : HausdorffSourceSpace → ℝ) :
    ∫ z, f z ∂egbFixedChargeAGibbsCollisionHausdorffSource n m 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      (egbFixedChargeAGibbsConeScale n k m x y : ℝ) *
        ((x : ℝ) * f egbFixedChargeAGibbsCollisionSlowNode + (y : ℝ) * f egbFixedChargeAGibbsCollisionFastNode) := by
  rw [egbFixedChargeAGibbsCone_source_factorization, ← egbFixedChargeAGibbsConeSource_scale,
    egbFixedChargeAGibbsConeSource_integral]
  change ((egbFixedChargeAGibbsConeScale n k m x y : ℝ) * x) * _ +
    ((egbFixedChargeAGibbsConeScale n k m x y : ℝ) * y) * _ = _
  ring

/-- Actual source integrals tend to zero for every real test, without continuity or boundedness assumptions. -/
theorem egbFixedChargeAGibbsCone_source_integrals_tendsto_zero (n m : ℕ) (x y : NNReal)
    (f : HausdorffSourceSpace → ℝ) :
    Tendsto (fun k => ∫ z, f z ∂egbFixedChargeAGibbsCollisionHausdorffSource n m 1
      (egbFixedChargeAGibbsConeEnergy n k m x y)) atTop (nhds 0) := by
  have h := (egbFixedChargeAGibbsConeScale_tendsto_zero n m x y).mul_const
    ((x : ℝ) * f egbFixedChargeAGibbsCollisionSlowNode + (y : ℝ) * f egbFixedChargeAGibbsCollisionFastNode)
  simpa only [egbFixedChargeAGibbsCone_source_integral, zero_mul] using h

/-- The actual finite positive measure, with its weak topology retained by a named definition. -/
def egbFixedChargeAGibbsConeFiniteSource (n k m : ℕ) (x y : NNReal) : FiniteMeasure HausdorffSourceSpace :=
  ⟨egbFixedChargeAGibbsCollisionHausdorffSource n m 1 (egbFixedChargeAGibbsConeEnergy n k m x y), inferInstance⟩

/-- Every prescribed cone point is the exact rescaled survivor of actual finite measures converging weakly to zero. -/
theorem egbFixedChargeAGibbsCone_source_weak_tendsto_zero (n m : ℕ) (x y : NNReal) :
    Tendsto (fun k => egbFixedChargeAGibbsConeFiniteSource n k m x y) atTop (nhds 0) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun k => ∫ z, f z ∂egbFixedChargeAGibbsCollisionHausdorffSource n m 1
    (egbFixedChargeAGibbsConeEnergy n k m x y)) atTop (nhds (∫ z, f z ∂(0 : Measure HausdorffSourceSpace)))
  simpa using egbFixedChargeAGibbsCone_source_integrals_tendsto_zero n m x y f

end
end GaloisForLFunctions.HTGeometry
