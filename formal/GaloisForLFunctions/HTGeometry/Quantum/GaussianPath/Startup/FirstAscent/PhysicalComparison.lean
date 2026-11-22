import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.DisjointSites
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.IncidentMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.Semicircle
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound

/-! # What an arbitrary physical circuit gains over the empty circuit -/
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- At every signed time the improvement from s gates is charged to
at most 42s local coefficients. The support can depend on both time and circuit. -/
theorem circuit_advantage {n : ℕ} (u : PathShell n) (s : ℕ) (t : ℝ) :
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    ∃ L : Finset (PathLabel n), L.card ≤ 42*s ∧
      orbitCircuitDistance H 0 t ≤ orbitCircuitDistance H s t+2* |t| * (∑ l ∈ L, |u l|) := by
  intro H
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist
    (unitaryEvolution H.val t) s (orbitCircuitDistance H s t)).mpr le_rfl
  let S := C.touchedSites
  let K : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonianOnSites Sᶜ u⟩
  have hS : S.card ≤ 2*s := C.card_touchedSites_le.trans (Nat.mul_le_mul_left 2 hC)
  have hu : z • (C.eval : Reg (n+2)) ∈ unitary _ := by
    have hz' : conj z*z=1 := by rw [Complex.conj_mul',hz]; norm_num
    apply Matrix.mem_unitaryGroup_iff.mpr
    simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul,(Unitary.mem_iff.mp C.eval.2).2,
      smul_smul,Complex.star_def,hz',one_smul]
  obtain ⟨w,hw,hm⟩ := deleted_evolution_phase disjoint_compl_left H K
    (pathHamiltonianOnSites_isSiteSupported Sᶜ u) ⟨_,hu⟩ (C.isSiteSupported_touchedSites.complex_smul z) t
  refine ⟨S.biUnion pathIncidentLabels,(pathIncident_union_card S).trans ?_,?_⟩
  · omega
  · apply (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mp
    refine ⟨w,hw,TwoQubitCircuit.one _,le_rfl,?_⟩
    rw [TwoQubitCircuit.one_eval]
    exact hm.trans (add_le_add he (mul_le_mul_of_nonneg_left (incident_deletion S u) (by positivity)))

/-- Every circuit budget must pay the initial spectral-width chord apart
from the incident mass of at most 42 coefficients per gate. -/
theorem initial_circuit_floor {n : ℕ} (u : PathShell n) (s : ℕ) {t : ℝ} (ht : 0≤t) :
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let w := circuitHamiltonianSpectralWidth H
    t*w ≤ Real.pi → ∃ L : Finset (PathLabel n), L.card ≤ 42*s ∧
      2*Real.sin (t*w/4) ≤ orbitCircuitDistance H s t+2*t*(∑ l ∈ L, |u l|) := by
  intro H w hs
  obtain ⟨L,hL,he⟩ := circuit_advantage u s t
  change orbitCircuitDistance H 0 t ≤ orbitCircuitDistance H s t + 2* |t| * _ at he
  rw [empty_distance H ht hs,abs_of_nonneg ht] at he
  exact ⟨L,hL,he⟩

#print axioms circuit_advantage
#print axioms initial_circuit_floor
end
end GaloisForLFunctions.HTGeometry.FirstAscent
