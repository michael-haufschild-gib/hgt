import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.SnapshotLimit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.DilationInterval
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.PhysicalRays

/-! # Late scalar probabilities from the identity and the first crossing -/
open Set Filter MeasureTheory ProbabilityTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open SharpOccupation
noncomputable section

theorem scalar_ray_limit (k : ℕ) {e : ℝ} (he : 0<e) (he' : e<sqrt 2)
    (o : (PrefixIndex (k+1) → ℝ) → ℝ)
    (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) {b : ℝ} (hb : 1<b) :
    let D : ℕ := 2^(k+3)
    ∀ᵐ ω ∂pathPauliDisorderLaw, let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      Tendsto (fun t : ℝ => rayMass b {y | pathGateDistance (k+1) 0 y (o y+t) ≤ e} x)
        atTop (𝓝 ((b-1)*((D:ℝ)*physicalArc e^(D-1)))) := by
  intro D
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let x : PrefixIndex (k+1) → ℝ := fun i => u (pathCoeffEquiv (k+1) i)
  let A := (fun z : ℝ => z-(-o x)) ⁻¹' visitSet H 0 e
  obtain ⟨hA,hfrac⟩ := TrajectoryProfiles.translated_scalar_fraction H (hω k) he he' (-o x)
  have hlim := dilation_interval_limit (A:=A) hA _ (by simpa only [sub_zero] using hfrac 0) hb
  have hgen : numberedGenerator (k+1) x=H.val := numberedGenerator_shell u
  have hphys : A={v | pathGateDistance (k+1) 0 x (o x+v) ≤ e} := by
    ext v
    change HasProjectiveCircuitApproximation (k+3) e 0 (unitaryEvolution H.val (v-(-o x))) ↔
      pathGateDistance (k+1) 0 x (o x+v) ≤ e
    rw [hasProjectiveCircuitApproximation_iff_infDist,pathGateDistance,hgen,sub_neg_eq_add,add_comm v]
  apply hlim.congr
  intro t
  exact (congrArg (fun S : Set ℝ => (volume.restrict (Icc 1 b)).real ((fun a => a*t) ⁻¹' S)) hphys).trans
    (rayMass_of_covariant_origin (k+1) 0 o hcov x b t e).symm

private theorem measurable_sublevel_on_graph {ι : Type*} [Fintype ι]
    (d : (ι → ℝ) × ℝ → ℝ) (hd : Continuous d)
    (o : (ι → ℝ) → ℝ) (ho : Measurable o) (e t : ℝ) :
    MeasurableSet {x | d (x,o x+t) ≤ e} := by
  have hpair : Measurable (fun x : ι → ℝ => (x,o x+t)) :=
    (measurable_id' (α:=ι → ℝ)).prodMk (ho.add_const t)
  exact measurableSet_Iic.preimage (hd.measurable.comp hpair)

theorem measurable_origin_event (n s : ℕ) (e t : ℝ) (o : (PrefixIndex n → ℝ) → ℝ)
    (ho : Measurable o) : MeasurableSet {x | pathGateDistance n s x (o x+t) ≤ e} :=
  measurable_sublevel_on_graph (ι:=PrefixIndex n)
    (fun p => pathGateDistance n s p.1 p.2) (continuous_distance n s) o ho e t

private theorem moving_origin_snapshot (k : ℕ) {e : ℝ} (he : 0<e) (he' : e<sqrt 2)
    (o : (PrefixIndex (k+1) → ℝ) → ℝ) (ho : Measurable o)
    (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) :
    let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
    let D : ℕ := 2^(k+3)
    Tendsto (fun t : ℝ => μ.real {x | pathGateDistance (k+1) 0 x (o x+t) ≤ e})
      atTop (𝓝 ((D:ℝ)*physicalArc e^(D-1))) := by
  intro μ D
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let X := fun ω i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  exact snapshot_of_ray_limit X (gaussian_pauli_prefix_coordinates_law (k+1)) _
    (fun t => measurable_origin_event (k+1) 0 e t o ho) _
    (fun _ hb => scalar_ray_limit k he he' o hcov hb)

/-- For each prefix of at least three qubits and every positive error
below √2, the prescribed-date chance of an empty fit tends to its exact
time density. The same limit holds at a prescribed delay measured from
the actual first robust crossing of any gate budget. -/
theorem gaussian_late_scalar_probability (k j : ℕ) {e : ℝ} (he : 0<e) (he' : e<sqrt 2) :
    let n := k+1
    let D : ℕ := 2^(k+3)
    let p := (D:ℝ)*physicalArc e^(D-1)
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n j (9/80)
    Tendsto (fun t : ℝ => μ.real {x | pathGateDistance n 0 x t ≤ e}) atTop (𝓝 p) ∧
    Tendsto (fun t : ℝ => μ.real {x | pathGateDistance n 0 x (σ x+t) ≤ e}) atTop (𝓝 p) := by
  intro n D p μ σ
  constructor
  · simpa only [zero_add] using
      moving_origin_snapshot k he he' (fun _ => 0) measurable_const (fun _ _ _ => mul_zero _)
  · exact moving_origin_snapshot k he he' σ (measurable_crossingOrigin ..)
      (fun _ ha => smul_crossingOrigin n j (9/80) ha)

#print axioms gaussian_late_scalar_probability
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
