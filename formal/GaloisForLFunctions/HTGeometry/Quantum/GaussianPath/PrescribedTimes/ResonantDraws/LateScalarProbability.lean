import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.SnapshotLimit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.DilationInterval
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin

/-! # Late scalar probabilities from the identity and the first crossing -/
open Set Filter MeasureTheory ProbabilityTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open SharpOccupation DiagonalSynthesis
noncomputable section

private theorem moving_origin_snapshot (k : ℕ) {e : ℝ} (he : 0<e) (he' : e<sqrt 2)
    (o : (PrefixIndex (k+1) → ℝ) → ℝ) (ho : Measurable o)
    (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) :
    let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
    let D : ℕ := 2^(k+3)
    Tendsto (fun t : ℝ => μ.real {x | pathGateDistance (k+1) 0 x (o x+t) ≤ e})
      atTop (𝓝 ((D:ℝ)*physicalArc e^(D-1))) := by
  intro μ D
  let X := fun ω i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let E (t : ℝ) := {x | pathGateDistance (k+1) 0 x (o x+t) ≤ e}
  have hm (t : ℝ) : MeasurableSet (E t) := measurableSet_le
    ((continuous_distance (k+1) 0).measurable.comp (measurable_id.prodMk (ho.add_const t))) measurable_const
  apply snapshot_of_ray_limit X (gaussian_pauli_prefix_coordinates_law (k+1)) E hm
  intro b hb
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let x := X ω
  let A := (fun z : ℝ => z-(-o x)) ⁻¹' visitSet H 0 e
  obtain ⟨hA,hfrac⟩ := TrajectoryProfiles.translated_scalar_fraction H (hω k) he he' (-o x)
  have hlim := dilation_interval_limit (A:=A) hA _ (by simpa only [sub_zero] using hfrac 0) hb
  have hgen : numberedGenerator (k+1) x=H.val := numberedGenerator_shell u
  apply hlim.congr
  intro t
  change (volume.restrict (Icc 1 b)).real ((fun a => a*t) ⁻¹' A) =
    (volume.restrict (Icc 1 b)).real ((fun a : ℝ => a • x) ⁻¹' E t)
  rw [measureReal_restrict_apply' measurableSet_Icc,measureReal_restrict_apply' measurableSet_Icc]
  congr 1
  ext a
  by_cases ha : a∈Icc 1 b
  · have hpos := zero_lt_one.trans_le ha.1
    simp only [mem_inter_iff,ha,and_true,mem_preimage]
    change HasProjectiveCircuitApproximation (k+3) e 0 (unitaryEvolution H.val (a*t-(-o x))) ↔
      pathGateDistance (k+1) 0 (a • x) (o (a • x)+t) ≤ e
    rw [hasProjectiveCircuitApproximation_iff_infDist,distance_dilate,mul_add,hcov a hpos x,
      pathGateDistance,hgen,sub_neg_eq_add,add_comm (a*t)]
  · simp only [mem_inter_iff,ha,and_false]

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
  exact ⟨by simpa only [zero_add] using moving_origin_snapshot k he he' (fun _ => 0)
    measurable_const (fun _ _ _ => mul_zero _),
    moving_origin_snapshot k he he' σ (measurable_crossingOrigin ..)
      (fun _ ha => smul_crossingOrigin n j (9/80) ha)⟩

#print axioms gaussian_late_scalar_probability
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
