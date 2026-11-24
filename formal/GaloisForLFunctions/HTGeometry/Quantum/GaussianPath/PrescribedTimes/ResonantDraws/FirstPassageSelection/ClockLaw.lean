import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.Posterior
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Distribution of the true first passages after a late scalar observation -/
open Set Filter MeasureTheory ProbabilityTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
open SharpOccupation
noncomputable section

/-- Condition on fitting the empty circuit at a late prescribed delay
from the actual crossing. At every pair of deadlines, the
joint distribution of the onset and the first subsequent wait tends to
its original value, including at atoms of the joint distribution. -/
theorem gaussian_late_scalar_first_passage_law (k j s : ℕ) {ε : ℝ} (hε : 0<ε)
    (hε' : ε<sqrt 2) (u v : ℝ) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j s
    let B := {x | σ x≤u ∧ Δ x≤v}
    let E (t : ℝ) := {x | pathGateDistance n 0 x (σ x+t)≤ε}
    Tendsto (fun t => μ.real (B ∩ E t)/μ.real (E t)) atTop (𝓝 (μ.real B)) := by
  intro n μ σ Δ B E
  have hσ : Measurable σ := measurable_crossingOrigin ..
  have hΔ : Measurable Δ := measurable_crossingWait ..
  have h₁ : MeasurableSet (σ ⁻¹' Iic u) := measurableSet_Iic.preimage hσ
  have h₂ : MeasurableSet (Δ ⁻¹' Iic v) := measurableSet_Iic.preimage hΔ
  exact gaussian_late_empty_posterior k j hε hε' B (h₁.inter h₂)

#print axioms gaussian_late_scalar_first_passage_law
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
