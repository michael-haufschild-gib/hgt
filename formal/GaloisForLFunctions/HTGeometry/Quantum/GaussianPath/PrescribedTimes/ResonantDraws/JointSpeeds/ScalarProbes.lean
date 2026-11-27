import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.FirstExcursionLaw

/-! # Exact Bernoulli law for first scalar hits on an incommensurate observation schedule -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open ResonantDraws SharpOccupation
noncomputable section

/-- The scalar affordable fraction is independent of the eigenbasis. -/
theorem scalar_phase_mass (k : ℕ) {ε : ℝ} (hε : ε∈Ioo (0:ℝ) (Real.sqrt 2)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, let D : ℕ := 2^(k+3)
      affordablePhaseMass k 0 ε ω = (D:ℝ)*physicalArc ε^(D-1:ℕ) := by
  let o := fun _ : PrefixIndex (k+1)→ℝ => (0:ℝ)
  have ho (a : ℝ) (_ : 0<a) (x : PrefixIndex (k+1)→ℝ) : a*o (a • x)=o x := mul_zero _
  filter_upwards [budget_ray_limit k 0 ε o ho (b:=2) (by norm_num),
    scalar_ray_limit k hε.1 hε.2 o ho (b:=2) (by norm_num)] with ω h₁ h₂
  have h := tendsto_nhds_unique h₁ h₂
  simpa only [show (2:ℝ)-1=1 by norm_num,one_mul] using h

/-- For scalar returns the individual Haar fraction is deterministic.
Every finite pattern therefore has the exact independent Bernoulli limit,
even conditional on an arbitrarily rare history of the original prefix. -/
theorem scalar_probe_pattern {I : Type} [Fintype I] (k r : ℕ) {ε : ℝ}
    (hε : ε∈Ioo (0:ℝ) (Real.sqrt 2)) (c : I→ℝ) (hc : RationallyIndependentFrequency c)
    (afterReturn : Bool) (hit : I→Bool) (B : Set (PrefixIndex (k+1)→ℝ)) (hB : MeasurableSet B) :
    let n := k+1
    let P := nearHilbertContinuousCircuitBudget (k+3)
    let D : ℕ := 2^(k+3)
    let p := (D:ℝ)*physicalArc ε^(D-1:ℕ)
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n P (9/80)
    let o := fun x => if afterReturn then σ x+crossingWait n P r x else σ x
    Tendsto (fun t => μ.real (B ∩ {x | ∀ i, (pathGateDistance n 0 x (o x+c i*t)≤ε) ↔ hit i=true}))
      atTop (𝓝 (μ.real B*∏ i, if hit i then p else 1-p)) := by
  classical
  intro n P D p μ σ o
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  let w := fun ω => ∏ i, if hit i then affordablePhaseMass k 0 ε ω else 1-affordablePhaseMass k 0 ε ω
  let q := ∏ i, if hit i then p else 1-p
  have hev : (∫ ω in X ⁻¹' B, w ω ∂pathPauliDisorderLaw)=μ.real B*q := by
    have h : w =ᵐ[pathPauliDisorderLaw.restrict (X ⁻¹' B)] fun _ => q := by
      filter_upwards [ae_restrict_of_ae (s:=X ⁻¹' B) (scalar_phase_mass k hε)] with ω hw
      change affordablePhaseMass k 0 ε ω=p at hw
      simp only [w,q,hw]
    rw [integral_congr_ae h,setIntegral_const,smul_eq_mul,hX.measureReal_preimage hB.nullMeasurableSet]
  have hh := joint_first_excursion_snapshot k P c hc (fun _ => afterReturn) hit
    (fun _ => r) (fun _ => 0) (fun _ => ε) B hB
  change Tendsto _ atTop (𝓝 (∫ ω in X ⁻¹' B, w ω ∂pathPauliDisorderLaw)) at hh
  rwa [hev] at hh

#print axioms scalar_probe_pattern
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
