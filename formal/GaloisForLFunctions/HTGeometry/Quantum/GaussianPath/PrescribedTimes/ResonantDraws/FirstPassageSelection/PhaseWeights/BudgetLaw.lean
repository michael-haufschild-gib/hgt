import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Setwise
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateBudgetDistribution

/-! # Late gate-budget probabilities after selection on the original first excursion -/
open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open SharpOccupation FirstPassageSelection
noncomputable section

/-- The Haar probability of an affordable phase is integrable as a
function of the original disorder, without choosing a measurable eigenbasis. -/
theorem integrable_affordablePhaseMass (k s : ℕ) (ε : ℝ) :
    Integrable (affordablePhaseMass k s ε) pathPauliDisorderLaw := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let o := fun _ : PrefixIndex (k+1)→ℝ => (0:ℝ)
  let E := fun t => {x | pathGateDistance (k+1) s x (o x+t) ≤ ε}
  apply integrable_ray_weight X (gaussian_pauli_prefix_coordinates_law (k+1)).measurable E
    (fun t => measurable_origin_event (k+1) s ε t o measurable_const)
  simpa only [show (2:ℝ)-1=1 by norm_num,one_mul] using
    budget_ray_limit k s ε o (fun _ _ _ => mul_zero _) (b:=2) (by norm_num)

private theorem weighted_from_origin (k s : ℕ) (ε : ℝ)
    (o : (PrefixIndex (k+1) → ℝ) → ℝ) (ho : Measurable o)
    (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) :
    let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
    let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
    ∀ B : Set (PrefixIndex (k+1)→ℝ), MeasurableSet B →
      Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance (k+1) s x (o x+t) ≤ ε})) atTop
        (𝓝 (∫ ω in X ⁻¹' B, affordablePhaseMass k s ε ω ∂pathPauliDisorderLaw)) := by
  intro μ X
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let E (t : ℝ) := {x | pathGateDistance (k+1) s x (o x+t) ≤ ε}
  have hm (t : ℝ) : MeasurableSet (E t) := measurable_origin_event (k+1) s ε t o ho
  refine weighted_setwise_limit X (gaussian_pauli_prefix_coordinates_law (k+1)) E hm
    (affordablePhaseMass k s ε) (fun _ hb => budget_ray_limit k s ε o hcov hb)

/-- At late prescribed delays from the actual first crossing and first
return, every measurable selection of prefixes sees its own mixture
of Haar gate-count laws, including at positive gate budgets. -/
theorem gaussian_selected_budget_distribution (k j r s : ℕ) (ε : ℝ) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j r
    ∀ B : Set (PrefixIndex n→ℝ), MeasurableSet B →
      let p := ∫ ω in X ⁻¹' B, affordablePhaseMass k s ε ω ∂pathPauliDisorderLaw
      Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n s x (σ x+t)≤ε})) atTop (𝓝 p) ∧
      Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n s x (σ x+Δ x+t)≤ε})) atTop (𝓝 p) := by
  intro n μ X σ Δ B hB p
  have hσ (a : ℝ) (ha : 0<a) (x : PrefixIndex n→ℝ) : a*σ (a • x)=σ x :=
    smul_crossingOrigin n j (9/80) ha x
  have hΔ (a : ℝ) (ha : 0<a) (x : PrefixIndex n→ℝ) : a*Δ (a • x)=Δ x :=
    smul_crossingWait n j r ha x
  exact ⟨weighted_from_origin k s ε σ (measurable_crossingOrigin ..) hσ B hB,
    weighted_from_origin k s ε (fun x => σ x+Δ x)
      ((measurable_crossingOrigin ..).add (measurable_crossingWait ..))
      (fun a ha x => by rw [mul_add,hσ a ha x,hΔ a ha x]) B hB⟩

#print axioms gaussian_selected_budget_distribution
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
