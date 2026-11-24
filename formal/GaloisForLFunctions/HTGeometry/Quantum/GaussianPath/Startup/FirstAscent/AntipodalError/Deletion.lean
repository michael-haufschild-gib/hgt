import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.AntipodalError.UnitaryFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.PhysicalComparison

/-! # Complementary chord bought by a sparse physical circuit -/

open Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.AntipodalError
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Complementary chord of a physical gate budget. -/
def gateDeficit {N : ℕ} (H : selfAdjoint (Reg N)) (s : ℕ) (t : ℝ) :=
  sqrt (4-(orbitCircuitDistance H s t)^2)

private theorem anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    sqrt (4-b^2) ≤ sqrt (4-a^2) :=
  sqrt_le_sqrt (sub_le_sub_left (pow_le_pow_left₀ ha hab 2) _)

private theorem phase_mem {N : ℕ} {U : Reg N} (hU : U∈unitary (Reg N)) {z : ℂ} (hz : ‖z‖=1) :
    z • U ∈ unitary (Reg N) := by
  have hc : star z*z=1 := by rw [Complex.star_def,Complex.conj_mul',hz]; norm_num
  obtain ⟨hl,hr⟩ := Unitary.mem_iff.mp hU
  apply Unitary.mem_iff.mpr
  simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hc,
    (mul_comm z (star z)).trans hc,one_smul,hl,hr,and_self]

/-- At every signed time, the gain in the complementary chord is at most
twice the evolution error from deleting the touched sites. In particular
near an antipodal phase this controls the squared distance deficit. -/
theorem circuit_deficit_advantage {n : ℕ} (u : PathShell n) (s : ℕ) (t : ℝ) :
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    ∃ L : Finset (PathLabel n), L.card ≤ 42*s ∧
      gateDeficit H s t ≤ gateDeficit H 0 t+2*|t| *(∑ l ∈ L, |u l|) := by
  intro H
  let U := unitaryEvolution H.val t
  have hU : U∈unitary (Reg _) := unitaryEvolution_mem_unitary H.2 t
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist U s (orbitCircuitDistance H s t)).mpr le_rfl
  let Y := z • (C.eval : Reg _)
  let S := C.touchedSites
  let K : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonianOnSites Sᶜ u⟩
  let V := unitaryEvolution K.val t
  have hV : V ∈ unitary (Reg _) := unitaryEvolution_mem_unitary K.2 t
  have hY : Y ∈ unitary (Reg _) := phase_mem C.eval.2 hz
  obtain ⟨w,hw,hm⟩ := disjoint_unitary_phase disjoint_compl_left
    (isSiteSupported_unitaryEvolution (pathHamiltonianOnSites_isSiteSupported Sᶜ u) t)
    (C.isSiteSupported_touchedSites.complex_smul z) hY
  let Z := w • (1 : Reg (n+2))
  have hZ : Z∈unitary (Reg _) := phase_mem (Submonoid.one_mem _) hw
  have hscalar : orbitCircuitDistance H 0 t ≤ ‖U-Z‖ := by
    apply (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
    exact ⟨w,hw,TwoQubitCircuit.one _,le_rfl,by rw [TwoQubitCircuit.one_eval]; exact le_rfl⟩
  have h₁ : gateDeficit H s t ≤ deficit U Y := anti (norm_nonneg _) he
  have h₂ : deficit V Y ≤ deficit V Z := anti (norm_nonneg _) hm
  have h₃ : deficit U Z ≤ gateDeficit H 0 t := anti Metric.infDist_nonneg hscalar
  have hUV : ‖U-V‖ ≤ |t| *(∑ l ∈ S.biUnion pathIncidentLabels, |u l|) :=
    (norm_unitaryEvolution_sub_le H.val K.val H.2 K.2 t).trans
      (mul_le_mul_of_nonneg_left (incident_deletion S u) (abs_nonneg _))
  have hcard : S.card ≤ 2*s := C.card_touchedSites_le.trans (Nat.mul_le_mul_left 2 hC)
  refine ⟨S.biUnion pathIncidentLabels,(pathIncident_union_card S).trans (by omega),?_⟩
  have h₄ := deficit_perturb U V Y hU hV hY
  have h₅ := deficit_perturb V U Z hV hU hZ
  rw [norm_sub_rev V U] at h₅
  linarith only [h₁,h₂,h₃,h₄,h₅,hUV]

#print axioms circuit_deficit_advantage
end
end GaloisForLFunctions.HTGeometry.FirstAscent.AntipodalError
