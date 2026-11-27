import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateScalarProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.GaussianOccupation

/-! # Late disorder distribution of the physical circuit cost -/
open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped Matrix.Norms.L2Operator ENNReal
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open SharpOccupation
noncomputable section

/-- Fraction of eigenphases affordable in the eigenbasis of this draw. -/
def affordablePhaseMass (k s : ℕ) (ε : ℝ) (ω : PathPauliDisorder) : ℝ :=
  let N := k+3
  let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  volume.real (projectiveContinuousCircuitCaptureTarget e (hermitianEigenbasisUnitary H.2.isHermitian) s ε)

private theorem translated_fraction {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (ε o p : ℝ)
    (h : Tendsto (fun T => visitFraction H s ε o (o+T)) atTop (𝓝 p)) :
    let A := (fun v : ℝ => v+o) ⁻¹' visitSet H s ε
    MeasurableSet A ∧ Tendsto (fun T : ℝ => volume.real (A ∩ Icc 0 T)/T) atTop (𝓝 p) := by
  intro A
  have hm : MeasurableSet (visitSet H s ε) := by
    have he : visitSet H s ε=(orbitCircuitDistance H s) ⁻¹' Iic ε :=
      Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist ..
    rw [he]
    exact measurableSet_Iic.preimage (orbitCircuitDistance_lipschitz H s).continuous.measurable
  refine ⟨hm.preimage (measurable_id.add_const o),h.congr fun T => ?_⟩
  have he : A ∩ Icc 0 T=(fun v : ℝ => v+o) ⁻¹' (visitSet H s ε ∩ Icc o (o+T)) := by
    ext v
    change (v+o∈visitSet H s ε ∧ 0≤v ∧ v≤T) ↔ v+o∈visitSet H s ε ∧ o≤v+o ∧ v+o≤o+T
    rw [add_comm o T,add_le_add_iff_right,le_add_iff_nonneg_left]
  rw [he,visitFraction,add_sub_cancel_left]
  exact congrArg (fun a : ℝ≥0∞ => a.toReal/T)
    ((measurePreserving_add_right volume o).measure_preimage (hm.inter measurableSet_Icc).nullMeasurableSet).symm

/-- Dilation samples the physical orbit over a growing interval after any
positively homogeneous clock of degree minus one. -/
theorem budget_ray_limit (k s : ℕ) (ε : ℝ)
    (o : (PrefixIndex (k+1) → ℝ) → ℝ)
    (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) {b : ℝ} (hb : 1<b) :
    let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
    let E := fun t => {x | pathGateDistance (k+1) s x (o x+t) ≤ ε}
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto (fun t => rayMass b (E t) (X ω)) atTop
      (𝓝 ((b-1)*affordablePhaseMass k s ε ω)) := by
  intro X E
  filter_upwards [PhaseBoundary.gaussian_uniform_affordable_fraction] with ω hw
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let x := X ω
  let A := (fun z : ℝ => z+o x) ⁻¹' visitSet H s ε
  obtain ⟨hA,hfrac⟩ := translated_fraction H s ε (o x) (affordablePhaseMass k s ε ω)
    (hw k s ε (fun _ => o x))
  have hh := dilation_interval_limit (A:=A) hA _ hfrac hb
  have hgen : numberedGenerator (k+1) x=H.val := numberedGenerator_shell u
  have hphys : A={v | pathGateDistance (k+1) s x (o x+v) ≤ ε} := by
    ext v
    change HasProjectiveCircuitApproximation (k+3) ε s (unitaryEvolution H.val (v+o x)) ↔
      pathGateDistance (k+1) s x (o x+v) ≤ ε
    rw [hasProjectiveCircuitApproximation_iff_infDist,pathGateDistance,hgen,add_comm v]
  apply hh.congr
  intro t
  exact (congrArg (fun S : Set ℝ => (volume.restrict (Icc 1 b)).real ((fun a => a*t) ⁻¹' S)) hphys).trans
    (rayMass_of_covariant_origin (k+1) s o hcov x b t ε).symm

private theorem late_from_origin (k s : ℕ) (ε : ℝ)
    (o : (PrefixIndex (k+1) → ℝ) → ℝ) (ho : Measurable o)
    (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) :
    let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
    Tendsto (fun t => μ.real {x | pathGateDistance (k+1) s x (o x+t) ≤ ε}) atTop
      (𝓝 (∫ ω, affordablePhaseMass k s ε ω ∂pathPauliDisorderLaw)) := by
  intro μ
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let X := fun ω i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let E (t : ℝ) := {x | pathGateDistance (k+1) s x (o x+t) ≤ ε}
  have hm (t : ℝ) : MeasurableSet (E t) := measurable_origin_event (k+1) s ε t o ho
  refine snapshot_of_random_ray_limit X (gaussian_pauli_prefix_coordinates_law (k+1)) E hm
    (affordablePhaseMass k s ε) ?_
  exact fun _ hb => budget_ray_limit k s ε o hcov hb

/-- At every tolerance and budget, the late prescribed-delay probability
converges to the mean affordable phase fraction of the same Gaussian
ensemble. This holds from identity, first crossing and first subsequent
low-budget return, with arbitrary crossing and return budgets. -/
theorem gaussian_late_budget_distribution (k j r s : ℕ) (ε : ℝ) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j r
    let p := ∫ ω, affordablePhaseMass k s ε ω ∂pathPauliDisorderLaw
    Tendsto (fun t => μ.real {x | pathGateDistance n s x t ≤ ε}) atTop (𝓝 p) ∧
    Tendsto (fun t => μ.real {x | pathGateDistance n s x (σ x+t) ≤ ε}) atTop (𝓝 p) ∧
    Tendsto (fun t => μ.real {x | pathGateDistance n s x ((σ x+Δ x)+t) ≤ ε}) atTop (𝓝 p) := by
  intro n μ σ Δ p
  have hσ (a : ℝ) (ha : 0<a) (x : PrefixIndex n → ℝ) : a*σ (a • x)=σ x :=
    smul_crossingOrigin n j (9/80) ha x
  have hΔ (a : ℝ) (ha : 0<a) (x : PrefixIndex n → ℝ) : a*Δ (a • x)=Δ x :=
    smul_crossingWait n j r ha x
  constructor
  · simpa only [zero_add] using
      late_from_origin k s ε (fun _ => 0) measurable_const (fun _ _ _ => mul_zero _)
  refine ⟨late_from_origin k s ε σ (measurable_crossingOrigin ..) hσ,?_⟩
  exact late_from_origin k s ε (fun x => σ x+Δ x)
      ((measurable_crossingOrigin ..).add (measurable_crossingWait ..))
      (fun a ha x => by rw [mul_add,hσ a ha x,hΔ a ha x])

#print axioms gaussian_late_budget_distribution
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
