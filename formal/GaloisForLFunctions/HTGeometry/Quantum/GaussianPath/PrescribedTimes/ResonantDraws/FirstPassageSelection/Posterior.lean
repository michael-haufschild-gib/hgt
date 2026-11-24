import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.SetwiseLimit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateScalarProbability

/-! # Posterior law of all sampled couplings after a late empty-circuit fit -/
open Set Filter MeasureTheory ProbabilityTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
open SharpOccupation
noncomputable section

/-- Observing an empty fit at a prescribed delay from the actual first
crossing asymptotically preserves the probability of every fixed
measurable event of the whole coupling vector. -/
theorem gaussian_late_empty_posterior (k j : ℕ) {ε : ℝ} (hε : 0<ε) (hε' : ε<sqrt 2) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n j (9/80)
    let E (t : ℝ) := {x | pathGateDistance n 0 x (σ x+t)≤ε}
    ∀ B : Set (PrefixIndex n → ℝ), MeasurableSet B →
      Tendsto (fun t => μ.real (B ∩ E t)/μ.real (E t)) atTop (𝓝 (μ.real B)) := by
  intro n μ σ E B hB
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let D : ℕ := 2^(k+3)
  let p := (D:ℝ)*physicalArc ε^(D-1)
  let X := fun ω i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hm (t : ℝ) : MeasurableSet (E t) := measurable_origin_event n 0 ε t σ (measurable_crossingOrigin ..)
  have hj := setwise_snapshot_limit X (gaussian_pauli_prefix_coordinates_law n) E hm p
    (fun _ hb => scalar_ray_limit k hε hε' σ (fun _ ha => smul_crossingOrigin n j (9/80) ha) hb) B hB
  have hp : 0<p := mul_pos (by dsimp only [D]; positivity) (pow_pos (physicalArc_spec hε hε').1.1 _)
  have hh := hj.div (gaussian_late_scalar_probability k j hε hε').2 hp.ne'
  rwa [mul_div_cancel_right₀ _ hp.ne'] at hh

#print axioms gaussian_late_empty_posterior
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
