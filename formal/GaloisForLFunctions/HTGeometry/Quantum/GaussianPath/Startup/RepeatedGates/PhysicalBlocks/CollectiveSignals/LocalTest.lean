import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.PacketData
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

/-! # A local reporter for the actual physical evolution at small angles -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open private probe_supported from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.RequiredPairs
open private triple_supported from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.LocalReplacement
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance packetTestAlgebra {N : ℕ} : CStarAlgebra (Reg N) where
variable {n : ℕ}

def packetTest (e f : Fin (n+1)) (i : Fin (n+2)) (t : ℝ) :=
  let V := unitaryEvolution (tripleGenerator e f) t
  star V*packetProbe e i*V*packetImage e f i

theorem packetTest_supported {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i : Fin (n+2)}
    (hi : i∈tripleSites e f) (t : ℝ) : IsSiteSupported (tripleSites e f) (packetTest e f i t) := by
  have hV := isSiteSupported_unitaryEvolution (triple_supported hm) t
  have hP := IsSiteSupported.mono (singleton_subset_iff.mpr hi) (probe_supported i (tripleAxis e i))
  exact IsSiteSupported.matrix_mul (IsSiteSupported.matrix_mul
    (IsSiteSupported.matrix_mul (IsSiteSupported.conjTranspose hV) hP) hV) (packetImage_supported hm hi)

theorem packetTest_unitary {e f : Fin (n+1)} (hm : e.succ=f.castSucc) (i : Fin (n+2)) (t : ℝ) :
    packetTest e f i t∈unitary _ := by
  have hV := unitaryEvolution_mem_unitary (tripleGenerator_selfAdjoint e f) t
  exact mul_mem (mul_mem (mul_mem (Unitary.star_mem hV) (finitePauliMatrix_mem_unitary _)) hV)
    (packetImage_unitary hm i)

private theorem isolated_packet_reporter {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i : Fin (n+2)}
    (hi : i∈tripleSites e f) (u : PathShell n) (t : ℝ) :
    let H := pathHamiltonianOnSites (tripleSites e f)ᶜ u
    let Z := unitaryEvolution (H+tripleGenerator e f) t
    let V := unitaryEvolution (tripleGenerator e f) t
    star Z*packetProbe e i*Z=star V*packetProbe e i*V := by
  intro H Z V
  let E := unitaryEvolution H t
  have hHS := pathHamiltonianOnSites_isSiteSupported (tripleSites e f)ᶜ u
  have he := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonianOnSites (tripleSites e f)ᶜ u) t
  have hc : Commute E (packetProbe e i) := commute_of_isSiteSupported_disjoint
    (disjoint_singleton_right.mpr (fun h => mem_compl.mp h hi))
    (isSiteSupported_unitaryEvolution hHS t) (probe_supported i (tripleAxis e i))
  have hfac : Z=E*V := unitaryEvolution_add_of_isSiteSupported_disjoint
    disjoint_compl_left hHS (triple_supported hm) t
  rw [hfac,star_mul]
  calc _ = star V*(star E*(packetProbe e i*E))*V := by simp only [mul_assoc]
       _ = _ := by rw [←hc.eq,←mul_assoc (star E) E,(Unitary.mem_iff.mp he).1,one_mul]

/-- The exterior Hamiltonian may be arbitrarily large. Only its couplings
to the tested triple enter the error in the Heisenberg reporter. -/
theorem packetTest_local_error {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i : Fin (n+2)}
    (hi : i∈tripleSites e f) (u : PathShell n) {δ : ℝ} (hδ : 0≤δ) (t : ℝ)
    (hbox : ∀ l∈(tripleSites e f).biUnion pathIncidentLabels,
      |u l-tripleField e f (1/sqrt 2) l|≤δ) :
    let U := unitaryEvolution (pathHamiltonian u) t
    ‖star U*packetProbe e i*U*packetImage e f i-packetTest e f i t‖≤126* |t| * δ := by
  intro U
  let H := pathHamiltonianOnSites (tripleSites e f)ᶜ u+tripleGenerator e f
  let Z := unitaryEvolution H t
  let P := packetProbe e i
  have hH : IsSelfAdjoint H := (isSelfAdjoint_pathHamiltonianOnSites _ u).add (tripleGenerator_selfAdjoint e f)
  have hU := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t
  have hZ := unitaryEvolution_mem_unitary hH t
  have herr := triple_local_error (e:=e) (f:=f) u (1/sqrt 2) δ hδ hbox
  rw [div_mul_cancel₀ _ (sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne',Complex.ofReal_one,one_smul] at herr
  have hdiff := (norm_unitaryEvolution_sub_le (pathHamiltonian u) H (isSelfAdjoint_pathHamiltonian u) hH t).trans
    (mul_le_mul_of_nonneg_left herr (abs_nonneg t))
  have hc := unitary_conjugation_norm_sub_le (star U) (star Z) P (Unitary.star_mem hU) (Unitary.star_mem hZ)
  rw [star_star,star_star,←star_sub,norm_star,show ‖P‖=1 from norm_finitePauliMatrix _,mul_one] at hc
  have he := hc.trans (mul_le_mul_of_nonneg_left hdiff two_pos.le)
  have hlocal := isolated_packet_reporter hm hi u t
  change star Z*P*Z=_ at hlocal
  rw [hlocal] at he
  change ‖(star U*P*U)*packetImage e f i-(star (unitaryEvolution (tripleGenerator e f) t)*P*
    unitaryEvolution (tripleGenerator e f) t)*packetImage e f i‖≤_
  rw [←sub_mul,CStarRing.norm_mul_mem_unitary _ (packetImage_unitary hm i)]
  exact he.trans_eq (by ring)

#print axioms packetTest_local_error
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
