import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.PhysicalLags
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.Averaging

/-! # An observed-occupation deadline for the first return of every static Hamiltonian -/

open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
open SharpOccupation
open PrecisionReturns (firstVisit firstVisit_isLeast)
noncomputable section

/-- The eigenbasis alone determines a floor for occupation on every
identity-start record. At the first return after an arbitrary origin,
all of that occupation occurred before the origin. -/
theorem static_observed_deadline {N d : ℕ} (i : (Fin N → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Register N)) (j s : ℕ) (hj : j + j ≤ s) {e : ℝ} (he : e ∈ Ioo (0:ℝ) 2) :
    let V := hermitianEigenbasisUnitary H.2.isHermitian
    let A := projectiveContinuousCircuitCaptureTarget i V j (zeroGateArcTolerance (physicalArc e/2))
    (∀ T ≥ (0:ℝ), volume.real A * T ≤ volume.real (visitSet H s e ∩ Icc 0 T)) ∧
      ∀ a ≥ (0:ℝ), volume.real A * firstVisit H a s e ≤ volume.real (visitSet H s e ∩ Icc 0 a) := by
  intro V A
  let E := H.2.isHermitian.eigenvalues ∘ i.symm
  let φ := RHTower.projectivePhysicalPhaseFlowHom E
  have diff (y t u) (ht : φ t+y ∈ A) (hu : φ u+y ∈ A) : t-u ∈ visitSet H s e := by
    obtain ⟨z,hz,C,hC,hfit⟩ := shifted_capture_difference i H j he y t u ht hu
    exact ⟨z,hz,C,hC.trans hj,hfit⟩
  have h := translated_window_floor φ (RHTower.uniformContinuous_projectivePhysicalPhaseFlow E).continuous
    A (isClosed_projectiveContinuousCircuitCaptureTarget ..) _ (closed_visits H s e).measurableSet diff
  refine ⟨h,?_⟩
  intro a ha
  have hw := h _ (ha.trans (firstVisit_isLeast H a s he.1).1.1)
  rwa [first_visit_mass H s he.1] at hw

#print axioms static_observed_deadline
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
